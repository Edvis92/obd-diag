"""
Simple OBD-II car diagnostic tool for Windows (works on Linux/macOS too).

Features: live data, read fault codes (DTCs), clear fault codes, demo mode.
Hardware: an ELM327-compatible adapter that shows up as a COM port
(USB, or Bluetooth after pairing it in Windows).

Setup:   pip install pyserial
Run:     python obd_diag.py
"""
import random
import re
import time
import tkinter as tk
from tkinter import messagebox, ttk

import serial
from serial.tools import list_ports

DEMO = "Demo (no car)"

# pid: (label, unit, decoder(bytes) -> value)
PIDS = {
    "0C": ("Engine RPM", "rpm", lambda d: (d[0] * 256 + d[1]) / 4),
    "0D": ("Vehicle speed", "km/h", lambda d: d[0]),
    "05": ("Coolant temp", "°C", lambda d: d[0] - 40),
    "0F": ("Intake air temp", "°C", lambda d: d[0] - 40),
    "04": ("Engine load", "%", lambda d: d[0] * 100 / 255),
    "11": ("Throttle position", "%", lambda d: d[0] * 100 / 255),
    "2F": ("Fuel level", "%", lambda d: d[0] * 100 / 255),
    "42": ("Battery voltage", "V", lambda d: (d[0] * 256 + d[1]) / 1000),
}

# A few common codes. Anything else: look it up by code number online.
DTC_INFO = {
    "P0300": "Random/multiple cylinder misfire",
    "P0301": "Cylinder 1 misfire",
    "P0302": "Cylinder 2 misfire",
    "P0303": "Cylinder 3 misfire",
    "P0304": "Cylinder 4 misfire",
    "P0171": "System too lean (bank 1)",
    "P0172": "System too rich (bank 1)",
    "P0420": "Catalyst efficiency below threshold (bank 1)",
    "P0442": "EVAP system small leak",
    "P0455": "EVAP system large leak",
    "P0113": "Intake air temp sensor high input",
    "P0128": "Coolant thermostat below regulating temp",
    "P0335": "Crankshaft position sensor circuit",
    "P0500": "Vehicle speed sensor malfunction",
}


class ELM327:
    def __init__(self, port, baud):
        self.ser = serial.Serial(port, baud, timeout=1)
        for c in ("ATZ", "ATE0", "ATL0", "ATS0", "ATH0", "ATSP0"):
            self.cmd(c, timeout=3)
        # First real request triggers protocol auto-detection (can take a while)
        if self.pid("00", timeout=15) is None:
            self.close()
            raise RuntimeError(
                "Adapter responded but the car did not.\n"
                "Check the adapter is plugged in and the ignition is ON."
            )

    def cmd(self, c, timeout=5):
        self.ser.reset_input_buffer()
        self.ser.write((c + "\r").encode())
        buf, end = b"", time.time() + timeout
        while time.time() < end and b">" not in buf:
            buf += self.ser.read(self.ser.in_waiting or 1)
        text = buf.decode(errors="ignore").replace(">", "")
        return [l.strip() for l in re.split(r"[\r\n]+", text) if l.strip()]

    @staticmethod
    def hexdata(lines):
        out = []
        for l in lines:
            l = re.sub(r"^[0-9A-F]:", "", l.upper().replace(" ", ""))
            if re.fullmatch(r"[0-9A-F]+", l) and len(l) % 2 == 0:
                out.append(l)  # odd-length lines are CAN length headers: skipped
        return "".join(out)

    def pid(self, pid, timeout=5):
        data = self.hexdata(self.cmd("01" + pid, timeout))
        i = data.find("41" + pid)
        if i < 0:
            return None
        return list(bytes.fromhex(data[i + 4:]))

    def read_dtcs(self):
        data = self.hexdata(self.cmd("03", timeout=8))
        if not data.startswith("43"):
            return []
        raw = list(bytes.fromhex(data[2:]))
        if len(raw) % 2:  # CAN adds a leading count byte
            raw = raw[1:]
        codes = []
        for hi, lo in zip(raw[::2], raw[1::2]):
            if hi == 0 and lo == 0:
                continue
            codes.append(f"{'PCBU'[hi >> 6]}{(hi >> 4) & 3}{hi & 0xF:X}{lo:02X}")
        return codes

    def clear_dtcs(self):
        self.cmd("04", timeout=8)

    def close(self):
        try:
            self.ser.close()
        except Exception:
            pass


class DemoCar:
    """Fake data so you can try the UI without a car."""

    codes = ["P0301", "P0420"]

    def pid(self, pid, timeout=0):
        t = time.time()
        rpm = int((850 + 300 * abs(__import__("math").sin(t / 3)) + random.randint(0, 40)) * 4)
        return {
            "0C": [rpm >> 8, rpm & 255],
            "0D": [int(40 + 20 * abs(__import__("math").sin(t / 5)))],
            "05": [90 + 40],
            "0F": [25 + 40],
            "04": [int(random.uniform(20, 40) * 2.55)],
            "11": [int(random.uniform(10, 20) * 2.55)],
            "2F": [int(62 * 2.55)],
            "42": [13800 >> 8, 13800 & 255],
        }.get(pid)

    def read_dtcs(self):
        return list(self.codes)

    def clear_dtcs(self):
        self.codes = []

    def close(self):
        pass


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("OBD-II Diagnostics")
        self.geometry("520x460")
        self.car = None
        self.pid_list = list(PIDS)
        self.idx = 0

        top = ttk.Frame(self, padding=8)
        top.pack(fill="x")
        ttk.Label(top, text="Port:").pack(side="left")
        self.port = ttk.Combobox(top, width=14, state="readonly")
        self.port.pack(side="left", padx=4)
        ttk.Button(top, text="↻", width=3, command=self.refresh_ports).pack(side="left")
        ttk.Label(top, text="Baud:").pack(side="left", padx=(8, 0))
        self.baud = ttk.Combobox(top, width=7, values=["38400", "115200", "9600"])
        self.baud.set("38400")
        self.baud.pack(side="left", padx=4)
        self.btn = ttk.Button(top, text="Connect", command=self.toggle)
        self.btn.pack(side="right")

        self.status = tk.StringVar(value="Not connected")
        ttk.Label(self, textvariable=self.status, padding=(8, 0)).pack(anchor="w")

        tabs = ttk.Notebook(self)
        tabs.pack(fill="both", expand=True, padx=8, pady=8)

        live = ttk.Frame(tabs, padding=12)
        tabs.add(live, text="Live data")
        self.vals = {}
        for r, (pid, (name, unit, _)) in enumerate(PIDS.items()):
            ttk.Label(live, text=name, font=("Segoe UI", 11)).grid(row=r, column=0, sticky="w", pady=3)
            v = tk.StringVar(value="—")
            ttk.Label(live, textvariable=v, font=("Segoe UI", 13, "bold"), width=10, anchor="e").grid(row=r, column=1, padx=10)
            ttk.Label(live, text=unit).grid(row=r, column=2, sticky="w")
            self.vals[pid] = v

        faults = ttk.Frame(tabs, padding=8)
        tabs.add(faults, text="Fault codes")
        bar = ttk.Frame(faults)
        bar.pack(fill="x")
        ttk.Button(bar, text="Read codes", command=self.read_codes).pack(side="left")
        ttk.Button(bar, text="Clear codes", command=self.clear_codes).pack(side="left", padx=6)
        self.out = tk.Text(faults, height=12, state="disabled", font=("Consolas", 10))
        self.out.pack(fill="both", expand=True, pady=(8, 0))

        self.refresh_ports()
        self.protocol("WM_DELETE_WINDOW", self.on_close)

    def refresh_ports(self):
        ports = [p.device for p in list_ports.comports()] + [DEMO]
        self.port["values"] = ports
        if not self.port.get():
            self.port.set(ports[0])

    def toggle(self):
        if self.car:
            self.disconnect()
            return
        self.status.set("Connecting… (can take up to 15 s)")
        self.update_idletasks()
        try:
            if self.port.get() == DEMO:
                self.car = DemoCar()
            else:
                self.car = ELM327(self.port.get(), int(self.baud.get()))
        except Exception as e:
            self.car = None
            self.status.set("Not connected")
            messagebox.showerror("Connection failed", str(e))
            return
        self.btn.config(text="Disconnect")
        self.status.set("Connected")
        self.poll()

    def disconnect(self):
        if self.car:
            self.car.close()
        self.car = None
        self.btn.config(text="Connect")
        self.status.set("Not connected")
        for v in self.vals.values():
            v.set("—")

    def poll(self):
        if not self.car:
            return
        pid = self.pid_list[self.idx % len(self.pid_list)]
        self.idx += 1
        try:
            d = self.car.pid(pid)
            if d:
                self.vals[pid].set(f"{PIDS[pid][2](d):.1f}")
            else:
                self.vals[pid].set("n/a")
        except Exception as e:
            self.disconnect()
            messagebox.showerror("Connection lost", str(e))
            return
        self.after(60, self.poll)

    def show(self, text):
        self.out.config(state="normal")
        self.out.delete("1.0", "end")
        self.out.insert("end", text)
        self.out.config(state="disabled")

    def read_codes(self):
        if not self.car:
            return messagebox.showinfo("Not connected", "Connect to the car first.")
        codes = self.car.read_dtcs()
        if not codes:
            self.show("No stored fault codes.")
        else:
            self.show("\n".join(f"{c}  {DTC_INFO.get(c, '(look up this code online)')}" for c in codes))

    def clear_codes(self):
        if not self.car:
            return messagebox.showinfo("Not connected", "Connect to the car first.")
        if messagebox.askyesno(
            "Clear codes",
            "This erases stored fault codes and resets readiness monitors.\n"
            "The check-engine light will return if the problem persists.\n\nContinue?",
        ):
            self.car.clear_dtcs()
            self.show("Codes cleared.")

    def on_close(self):
        self.disconnect()
        self.destroy()


if __name__ == "__main__":
    App().mainloop()