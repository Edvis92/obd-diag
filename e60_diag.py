"""
BMW E60 (built before 03/2007, K-line) diagnostic probe for K+DCAN cables.
READ-ONLY: it only identifies modules and reads fault memory. It never
codes, clears, flashes or writes anything to the car.

This is a FIRST VERSION written without access to a real car. Every message
sent and received is shown in the log (and saved to e60_log.txt in your user
folder), so if something doesn't work we can fix it from the log.

Setup:   pip install pyserial
Run:     python e60_diag.py
"""
import os
import queue
import threading
import time
import tkinter as tk
from tkinter import messagebox, ttk

import serial
from serial.tools import list_ports

BAUD = 10400
TESTER = 0xF1

# Common E60 module addresses (not verified on your car; use Scan to see who answers)
MODULES = {
    "00 ZGM gateway": 0x00,
    "12 DME engine": 0x12,
    "18 EGS gearbox": 0x18,
    "34 DSC stability": 0x34,
    "5B IHKA climate": 0x5B,
    "60 KOMBI cluster": 0x60,
}

NRC = {
    0x10: "general reject",
    0x11: "service not supported",
    0x12: "sub-function not supported",
    0x22: "conditions not correct",
    0x31: "request out of range",
    0x33: "security access denied",
    0x78: "response pending",
}


def hx(b):
    return " ".join(f"{x:02X}" for x in b)


def wait(seconds):
    end = time.perf_counter() + seconds
    while time.perf_counter() < end:
        pass


class KLine:
    def __init__(self, port, log):
        self.log = log
        self.pending = bytearray()
        self.ser = serial.Serial(port, BAUD, bytesize=8, parity="N", stopbits=1, timeout=0.2)

    def close(self):
        try:
            self.ser.close()
        except Exception:
            pass

    @staticmethod
    def frame(target, data):
        n = len(data)
        hdr = [0x80 | n, target, TESTER] if n <= 63 else [0x80, target, TESTER, n]
        msg = hdr + list(data)
        msg.append(sum(msg) & 0xFF)
        return bytes(msg)

    def get(self, n, timeout):
        out = bytearray()
        while self.pending and len(out) < n:
            out.append(self.pending.pop(0))
        end = time.time() + timeout
        while len(out) < n and time.time() < end:
            out += self.ser.read(n - len(out))
        return bytes(out)

    def send(self, msg):
        self.ser.reset_input_buffer()
        self.pending = bytearray()
        self.ser.write(msg)
        self.ser.flush()
        self.log("TX " + hx(msg))
        echo = self.get(len(msg), 0.3)  # K-line cables normally echo what we send
        if echo != msg:
            self.pending = bytearray(echo)  # no echo: this is already (part of) a reply

    def recv(self, timeout=1.5):
        h = self.get(1, timeout)
        if not h:
            return None
        rest = self.get(2, 0.3)
        if len(rest) < 2:
            self.log("RX incomplete header: " + hx(h + rest))
            return None
        n = h[0] & 0x3F
        extra = b""
        if n == 0:
            extra = self.get(1, 0.3)
            if not extra:
                return None
            n = extra[0]
        data = self.get(n, 0.5)
        cs = self.get(1, 0.3)
        raw = h + rest + extra + data + cs
        self.log("RX " + hx(raw))
        if len(data) < n or not cs:
            self.log("   (incomplete reply)")
            return None
        if (sum(raw[:-1]) & 0xFF) != cs[0]:
            self.log("   (checksum mismatch)")
        return data

    def request(self, target, data):
        self.send(self.frame(target, data))
        for _ in range(20):
            r = self.recv()
            if r is None:
                return None
            if len(r) >= 3 and r[0] == 0x7F and r[2] == 0x78:
                self.log("   (module busy, waiting)")
                continue
            return r
        return None

    def start(self, target):
        """Fast init (25 ms low / 25 ms high), then StartCommunication."""
        self.ser.reset_input_buffer()
        self.ser.break_condition = True
        wait(0.025)
        self.ser.break_condition = False
        wait(0.025)
        r = self.request(target, [0x81])
        return bool(r) and r[0] == 0xC1

    def stop(self, target):
        try:
            self.request(target, [0x82])
        except Exception:
            pass


def ascii_part(b):
    s = "".join(chr(x) if 32 <= x < 127 else "." for x in b)
    return s


def decode_dtc(hi, lo):
    return f"{'PCBU'[hi >> 6]}{(hi >> 4) & 3}{hi & 0xF:X}{lo:02X}"


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("BMW E60 K-line diagnostics (read-only)")
        self.geometry("640x560")
        self.k = None
        self.busy = False
        self.q = queue.Queue()
        self.logfile = os.path.join(os.path.expanduser("~"), "e60_log.txt")

        top = ttk.Frame(self, padding=8)
        top.pack(fill="x")
        ttk.Label(top, text="Port:").pack(side="left")
        self.port = ttk.Combobox(top, width=10, state="readonly")
        self.port.pack(side="left", padx=4)
        ttk.Button(top, text="↻", width=3, command=self.refresh).pack(side="left")
        self.btn = ttk.Button(top, text="Open port", command=self.toggle)
        self.btn.pack(side="left", padx=8)
        ttk.Label(top, text="Module:").pack(side="left", padx=(8, 0))
        self.mod = ttk.Combobox(top, width=18, values=list(MODULES))
        self.mod.set("12 DME engine")
        self.mod.pack(side="left", padx=4)

        bar = ttk.Frame(self, padding=(8, 0))
        bar.pack(fill="x")
        ttk.Button(bar, text="Scan modules", command=lambda: self.run(self.scan)).pack(side="left")
        ttk.Button(bar, text="Identify", command=lambda: self.run(self.ident)).pack(side="left", padx=6)
        ttk.Button(bar, text="Read faults", command=lambda: self.run(self.faults)).pack(side="left")
        ttk.Button(bar, text="Copy log", command=self.copy).pack(side="right")

        self.text = tk.Text(self, font=("Consolas", 10), state="disabled")
        self.text.pack(fill="both", expand=True, padx=8, pady=8)

        self.refresh()
        self.log(f"Log is also saved to {self.logfile}")
        self.log("Steps: plug cable into car, ignition ON, pick port, Open port, then Scan modules.")
        self.after(100, self.drain)
        self.protocol("WM_DELETE_WINDOW", self.on_close)

    # ---- logging (thread safe) ----
    def log(self, s):
        self.q.put(f"{time.strftime('%H:%M:%S')}  {s}")

    def drain(self):
        lines = []
        while not self.q.empty():
            lines.append(self.q.get())
        if lines:
            block = "\n".join(lines) + "\n"
            self.text.config(state="normal")
            self.text.insert("end", block)
            self.text.see("end")
            self.text.config(state="disabled")
            try:
                with open(self.logfile, "a", encoding="utf-8") as f:
                    f.write(block)
            except Exception:
                pass
        self.after(100, self.drain)

    def copy(self):
        self.clipboard_clear()
        self.clipboard_append(self.text.get("1.0", "end"))

    # ---- port ----
    def refresh(self):
        ports = [p.device for p in list_ports.comports()]
        self.port["values"] = ports
        if ports and not self.port.get():
            self.port.set(ports[0])

    def toggle(self):
        if self.k:
            self.k.close()
            self.k = None
            self.btn.config(text="Open port")
            self.log("Port closed")
            return
        try:
            self.k = KLine(self.port.get(), self.log)
        except Exception as e:
            messagebox.showerror("Cannot open port", str(e))
            return
        self.btn.config(text="Close port")
        self.log(f"Port {self.port.get()} open at {BAUD} baud")

    def target(self):
        try:
            return int(self.mod.get().split()[0], 16)
        except Exception:
            raise ValueError("Type the module address as two hex digits, e.g. 12")

    def run(self, fn):
        if not self.k:
            return messagebox.showinfo("Port closed", "Press Open port first.")
        if self.busy:
            return
        self.busy = True

        def work():
            try:
                fn()
            except Exception as e:
                self.log(f"ERROR: {e}")
            finally:
                self.busy = False

        threading.Thread(target=work, daemon=True).start()

    # ---- actions ----
    def scan(self):
        self.log("--- Scan: asking each common module to answer ---")
        found = 0
        for name, addr in MODULES.items():
            self.log(f"Trying {name}")
            if self.k.start(addr):
                self.log(f"   >>> {name} ANSWERED")
                found += 1
                self.k.stop(addr)
            time.sleep(0.5)
        self.log(f"--- Scan done, {found} module(s) answered ---")

    def ident(self):
        t = self.target()
        self.log(f"--- Identify module {t:02X} ---")
        if not self.k.start(t):
            return self.log("No answer from module (see TX/RX lines above)")
        r = self.k.request(t, [0x1A, 0x80])
        if r and r[0] == 0x5A:
            self.log("Identification text: " + ascii_part(r[2:]))
        else:
            self.explain(r)
        self.k.stop(t)

    def faults(self):
        t = self.target()
        self.log(f"--- Fault memory of module {t:02X} ---")
        if not self.k.start(t):
            return self.log("No answer from module (see TX/RX lines above)")
        r = self.k.request(t, [0x18, 0x00, 0xFF, 0x00])
        if r and r[0] == 0x58:
            n = r[1] if len(r) > 1 else 0
            body = r[2:]
            if n == 0:
                self.log("No stored faults reported.")
            for i in range(0, len(body) - 2, 3):
                hi, lo, st = body[i], body[i + 1], body[i + 2]
                self.log(f"Fault raw {hi:02X}{lo:02X} status {st:02X}  (as OBD code: {decode_dtc(hi, lo)})")
            self.log("BMW's own fault numbers need BMW's tables. Send me this log to map them.")
        else:
            self.explain(r)
        self.k.stop(t)

    def explain(self, r):
        if r is None:
            self.log("No reply.")
        elif r[0] == 0x7F and len(r) >= 3:
            self.log(f"Module refused: {NRC.get(r[2], hex(r[2]))}")
        else:
            self.log("Unexpected reply: " + hx(r))

    def on_close(self):
        if self.k:
            self.k.close()
        self.destroy()


if __name__ == "__main__":
    App().mainloop()
