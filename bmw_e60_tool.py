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
import sys
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


DEMO = "Demo (no car)"


class FakeSerial:
    """Pretends to be a car so you can try the program without one."""

    PRESENT = {
        0x00: b"DEMO ZGM 0000001",
        0x12: b"DEMO DME 0000002",
        0x18: b"DEMO EGS 0000003",
        0x34: b"DEMO DSC 0000004",
    }
    FAULTS = {0x12: [(0x01, 0x71, 0x2F), (0x04, 0x20, 0x2F)], 0x34: [(0x05, 0x00, 0x2F)]}

    def __init__(self):
        self.buf = bytearray()
        self.break_condition = False

    def reset_input_buffer(self):
        self.buf = bytearray()

    def flush(self):
        pass

    def close(self):
        pass

    def read(self, n):
        if not self.buf:
            time.sleep(0.01)
            return b""
        out = bytes(self.buf[:n])
        del self.buf[:n]
        return out

    def reply(self, module, data):
        msg = [0x80 | len(data), TESTER, module] + list(data)
        msg.append(sum(msg) & 0xFF)
        self.buf += bytes(msg)

    def write(self, msg):
        time.sleep(0.02)
        self.buf += msg  # echo, like a real K-line cable
        n = msg[0] & 0x3F
        module, data = msg[1], list(msg[3:3 + n])
        if module not in self.PRESENT or not data:
            return
        if data[0] == 0x81:
            self.reply(module, [0xC1, 0xEF, 0x8F])
        elif data[0] == 0x82:
            self.reply(module, [0xC2])
        elif data[:2] == [0x1A, 0x80]:
            self.reply(module, [0x5A, 0x80] + list(self.PRESENT[module]))
        elif data[0] == 0x18:
            faults = self.FAULTS.get(module, [])
            body = [x for f in faults for x in f]
            self.reply(module, [0x58, len(faults)] + body)
        else:
            self.reply(module, [0x7F, data[0], 0x11])


class KLine:
    def __init__(self, port, log):
        self.log = log
        self.pending = bytearray()
        if port == DEMO:
            self.ser = FakeSerial()
        else:
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


BG = "#14151a"
PANEL = "#1d1f26"
FIELD = "#2a2d37"
FG = "#e6e8ee"
MUTED = "#8b90a0"
ACCENT = "#1c69d4"


def app_dir():
    base = sys.executable if getattr(sys, "frozen", False) else os.path.abspath(__file__)
    return os.path.dirname(base)


def draw_car(c, ox=0, oy=0):
    """A simple side-view sedan drawing (front of the car on the right)."""

    def P(*pts):
        return [v + (ox if i % 2 == 0 else oy) for i, v in enumerate(pts)]

    c.create_polygon(
        P(8, 66, 8, 50, 40, 44, 70, 40, 96, 16, 172, 16, 204, 40, 244, 46, 256, 58, 252, 66),
        fill="#4b5263", outline="",
    )
    c.create_polygon(P(80, 38, 100, 20, 170, 20, 194, 38), fill="#9fb4d0", outline="")
    c.create_line(P(134, 20, 134, 38), fill="#4b5263", width=3)
    c.create_line(P(12, 56, 250, 56), fill=ACCENT, width=2)
    c.create_rectangle(P(8, 48, 14, 54), fill="#d9463e", outline="")
    c.create_rectangle(P(246, 48, 255, 54), fill="#f4f1dd", outline="")
    for cx in (60, 204):
        c.create_oval(P(cx - 18, 50, cx + 18, 86), fill=BG, outline="")
        c.create_oval(P(cx - 15, 53, cx + 15, 83), fill="#262830", outline=MUTED, width=2)
        c.create_oval(P(cx - 6, 62, cx + 6, 74), fill=MUTED, outline="")


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("BMW E60 diagnostics (read-only)")
        self.geometry("720x680")
        self.minsize(640, 520)
        self.k = None
        self.busy = False
        self.q = queue.Queue()
        self.logfile = os.path.join(os.path.expanduser("~"), "e60_log.txt")
        self.style_ui()

        # header with title and car picture
        head = tk.Frame(self, bg=BG)
        head.pack(fill="x")
        left = tk.Frame(head, bg=BG)
        left.pack(side="left", padx=18, pady=14)
        tk.Label(left, text="BMW E60", font=("Segoe UI", 24, "bold"), fg=FG, bg=BG).pack(anchor="w")
        tk.Label(left, text="K-line diagnostics  ·  read-only", font=("Segoe UI", 10), fg=MUTED, bg=BG).pack(anchor="w")
        self.art = tk.Canvas(head, width=290, height=100, bg=BG, highlightthickness=0)
        self.art.pack(side="right", padx=14)
        self.show_art()

        self.status = tk.StringVar(value="Port closed")
        tk.Label(self, textvariable=self.status, anchor="w", bg=BG, fg=MUTED, padx=14, pady=5).pack(side="bottom", fill="x")

        ctl = ttk.Frame(self, padding=(14, 12, 14, 4))
        ctl.pack(fill="x")
        ttk.Label(ctl, text="PORT", style="Muted.TLabel").grid(row=0, column=0, sticky="w")
        ttk.Label(ctl, text="MODULE", style="Muted.TLabel").grid(row=0, column=3, sticky="w", padx=(18, 0))
        self.port = ttk.Combobox(ctl, width=16, state="readonly")
        self.port.grid(row=1, column=0)
        ttk.Button(ctl, text="↻", width=3, command=self.refresh).grid(row=1, column=1, padx=4)
        self.btn = ttk.Button(ctl, text="Open port", style="Accent.TButton", command=self.toggle)
        self.btn.grid(row=1, column=2, padx=(4, 0))
        self.mod = ttk.Combobox(ctl, width=20, values=list(MODULES))
        self.mod.set("12 DME engine")
        self.mod.grid(row=1, column=3, padx=(18, 0))

        acts = ttk.Frame(self, padding=(14, 8))
        acts.pack(fill="x")
        ttk.Button(acts, text="Scan modules", style="Accent.TButton", command=lambda: self.run(self.scan)).pack(side="left")
        ttk.Button(acts, text="Identify", command=lambda: self.run(self.ident)).pack(side="left", padx=8)
        ttk.Button(acts, text="Read faults", command=lambda: self.run(self.faults)).pack(side="left")
        ttk.Button(acts, text="Copy log", command=self.copy).pack(side="right")

        box = ttk.Frame(self, padding=(14, 4, 14, 8))
        box.pack(fill="both", expand=True)
        self.text = tk.Text(
            box, font=("Consolas", 10), state="disabled", bg="#0f1014", fg=FG,
            relief="flat", padx=10, pady=8, wrap="word", insertbackground=FG,
        )
        sb = ttk.Scrollbar(box, command=self.text.yview)
        self.text.config(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        self.text.pack(side="left", fill="both", expand=True)
        self.text.tag_config("tx", foreground="#7f8598")
        self.text.tag_config("rx", foreground="#8fd19e")
        self.text.tag_config("head", foreground="#6aa9ff", font=("Consolas", 10, "bold"))
        self.text.tag_config("good", foreground="#4cd964", font=("Consolas", 10, "bold"))
        self.text.tag_config("bad", foreground="#ff6b6b")

        self.refresh()
        self.log(f"Log is also saved to {self.logfile}")
        self.log("Steps: plug cable into car, ignition ON, pick port, Open port, then Scan modules.")
        self.log("No car handy? Pick 'Demo (no car)' as the port to try the program with fake data.")
        self.after(100, self.drain)
        self.protocol("WM_DELETE_WINDOW", self.on_close)

    def style_ui(self):
        self.configure(bg=PANEL)
        st = ttk.Style(self)
        st.theme_use("clam")
        st.configure(".", background=PANEL, foreground=FG, fieldbackground=FIELD, font=("Segoe UI", 10))
        st.configure("TFrame", background=PANEL)
        st.configure("TLabel", background=PANEL, foreground=FG)
        st.configure("Muted.TLabel", foreground=MUTED, font=("Segoe UI", 8, "bold"))
        st.configure("TButton", background="#2f323d", foreground=FG, padding=(14, 7), borderwidth=0, focuscolor=PANEL)
        st.map("TButton", background=[("active", "#3b3f4d")])
        st.configure("Accent.TButton", background=ACCENT, foreground="white")
        st.map("Accent.TButton", background=[("active", "#2a7de8")])
        st.configure("TCombobox", fieldbackground=FIELD, background="#2f323d", foreground=FG, arrowcolor=FG, padding=5)
        st.map("TCombobox", fieldbackground=[("readonly", FIELD)], foreground=[("readonly", FG)])
        st.configure("Vertical.TScrollbar", background="#2f323d", troughcolor=PANEL, arrowcolor=FG)
        self.option_add("*TCombobox*Listbox.background", FIELD)
        self.option_add("*TCombobox*Listbox.foreground", FG)

    def show_art(self):
        """Shows e60.png from the program's folder if you put one there, else a drawing."""
        try:
            img = tk.PhotoImage(file=os.path.join(app_dir(), "e60.png"))
            f = max(-(-img.width() // 280), -(-img.height() // 100), 1)
            self.photo = img.subsample(f)
            self.art.create_image(145, 50, image=self.photo)
        except Exception:
            draw_car(self.art, 16, 6)

    # ---- logging (thread safe) ----
    def log(self, s):
        self.q.put(f"{time.strftime('%H:%M:%S')}  {s}")

    @staticmethod
    def tag_for(line):
        body = line[10:].strip()
        if body.startswith("TX"):
            return "tx"
        if body.startswith("RX"):
            return "rx"
        if body.startswith("---"):
            return "head"
        if ">>>" in body:
            return "good"
        if body.startswith(("ERROR", "No answer", "No reply", "Module refused", "Unexpected")):
            return "bad"
        return ""

    def drain(self):
        lines = []
        while not self.q.empty():
            item = self.q.get()
            if isinstance(item, tuple):
                self.status.set(item[1])
            else:
                lines.append(item)
        if lines:
            self.text.config(state="normal")
            for line in lines:
                tag = self.tag_for(line)
                self.text.insert("end", line + "\n", (tag,) if tag else ())
            self.text.see("end")
            self.text.config(state="disabled")
            try:
                with open(self.logfile, "a", encoding="utf-8") as f:
                    f.write("\n".join(lines) + "\n")
            except Exception:
                pass
        self.after(100, self.drain)

    def copy(self):
        self.clipboard_clear()
        self.clipboard_append(self.text.get("1.0", "end"))

    # ---- port ----
    def refresh(self):
        ports = [p.device for p in list_ports.comports()] + [DEMO]
        self.port["values"] = ports
        if not self.port.get():
            self.port.set(ports[0])

    def toggle(self):
        if self.k:
            self.k.close()
            self.k = None
            self.btn.config(text="Open port")
            self.status.set("Port closed")
            self.log("Port closed")
            return
        try:
            self.k = KLine(self.port.get(), self.log)
        except Exception as e:
            messagebox.showerror("Cannot open port", str(e))
            return
        self.btn.config(text="Close port")
        self.status.set(f"Port {self.port.get()} open  ·  ready")
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
            self.q.put(("status", "Working…"))
            try:
                fn()
            except Exception as e:
                self.log(f"ERROR: {e}")
            finally:
                self.busy = False
                self.q.put(("status", "Ready"))

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
