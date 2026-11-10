"""
BMW E60 diagnostics for K+DCAN cables (K-line, cars built before 03/2007).
READ-ONLY: finds control units, identifies them and reads fault memory, then
shows what each fault means using the built-in BMW fault database.
It never codes, clears, flashes or writes anything to the car.

Setup:   pip install pyserial
Run:     python e60_full.py     (needs e60_data.db in the same folder)
"""
import os
import queue
import re
import sqlite3
import sys
import threading
import time
import tkinter as tk
import webbrowser
from tkinter import messagebox, ttk
from urllib.parse import quote_plus

import serial
from serial.tools import list_ports

BAUD = 10400
TESTER = 0xF1
DEMO = "Demo (no car)"
AUTO = "Auto (show every variant that knows this code)"

ADDR_NAMES = {
    0x00: "Body gateway (KGM/ZGM)", 0x01: "Airbag (ACSM/MRS)", 0x02: "Steering column switch (SZL)",
    0x05: "Driver door", 0x06: "Passenger door", 0x12: "Engine (DME/DDE)", 0x16: "Active steering (AFS)",
    0x17: "Fuel pump module (EKP)", 0x18: "Gearbox (EGS)", 0x20: "Tyre pressure (RDC)",
    0x21: "Cruise control (ACC)", 0x22: "Adaptive light (ALC)", 0x23: "Roll stabilisation (ARS)",
    0x29: "Stability control (DSC)", 0x40: "Car access (CAS)", 0x41: "Alarm (DWA)",
    0x60: "Instrument cluster (KOMBI)", 0x63: "Navigation / MMI (CCC)", 0x64: "Park distance (PDC)",
    0x70: "Light module (LM)", 0x72: "Body base module (KBM)", 0x73: "Central info display (CID)",
    0x78: "Climate (IHKA)",
}
QUICK = [0x00, 0x01, 0x02, 0x05, 0x06, 0x12, 0x18, 0x29, 0x40, 0x60, 0x64, 0x70, 0x72, 0x78]

NRC = {
    0x10: "general reject", 0x11: "service not supported", 0x12: "sub-function not supported",
    0x22: "conditions not correct", 0x31: "request out of range", 0x33: "security access denied",
    0x78: "response pending",
}

# ---------------------------------------------------------------------------
# Rough German -> English helper for fault texts that BMW only ships in German.
# It translates known words and word parts; anything unknown stays German.
# ---------------------------------------------------------------------------
WORDS = {  # whole words only
    "vor": "before", "nach": "after", "und": "and", "oder": "or", "mit": "with",
    "ohne": "without", "bei": "at", "von": "from", "fuer": "for", "ueber": "above",
    "nicht": "not", "kein": "no", "keine": "no", "zu": "too", "ist": "is",
    "links": "left", "rechts": "right", "hinten": "rear", "vorne": "front",
    "aus": "off", "ein": "on", "aktiv": "active", "fehler": "fault", "fehlt": "missing",
    "defekt": "defective", "falsch": "wrong", "falsche": "wrong", "hoch": "high",
    "niedrig": "low", "wegen": "due to", "gegen": "to", "masse": "ground",
    "plus": "positive", "intern": "internal", "interne": "internal", "interner": "internal",
    "botschaft": "message", "nachricht": "message", "telegramm": "message",
    "signal": "signal", "bereich": "range", "zustand": "state", "typ": "type",
    "sendet": "sends", "empfangen": "received", "erkannt": "detected",
    "begrenzt": "limited", "vorhanden": "present", "werden": "are", "wurde": "was",
    "konnte": "could", "mehrere": "several", "anzahl": "number", "alterung": "ageing", "test": "test",
}

STEMS = [  # parts of words, matched inside longer words (longest first is applied)
    ("abgasrueckfuehr", "EGR"), ("abgasrückführ", "EGR"), ("abgastemperatur", "exhaust temperature "),
    ("abgasgegendruck", "exhaust back pressure "), ("abgasklappe", "exhaust flap "), ("abgas", "exhaust gas "),
    ("ansauglufttemperatur", "intake air temperature "), ("ansaugluft", "intake air "),
    ("ladelufttemperatur", "charge air temperature "), ("ladedruck", "boost pressure "),
    ("umgebungsdruck", "ambient pressure "), ("umgebungstemperatur", "ambient temperature "),
    ("kuehlmitteltemperatur", "coolant temperature "), ("kuehlmittel", "coolant "),
    ("oeltemperatur", "oil temperature "), ("oelqualitaet", "oil quality "), ("oelniveau", "oil level "),
    ("oeldruck", "oil pressure "), ("raildruck", "rail pressure "), ("hochdruck", "high pressure "),
    ("niederdruck", "low pressure "), ("kraftstoffpumpe", "fuel pump "), ("kraftstoff", "fuel "),
    ("lambdasondenbeheizung", "oxygen sensor heater "), ("lambdasondenheizung", "oxygen sensor heater "),
    ("lambdasonde", "oxygen sensor "), ("katalysator", "catalyst "), ("partikelfilter", "particulate filter "),
    ("stickoxid", "NOx "), ("luftmassenmesser", "mass air flow sensor "), ("luftmasse", "air mass "),
    ("drosselklappen", "throttle valve "), ("drosselklappe", "throttle valve "), ("drallklappen", "swirl flap "),
    ("kurbelwellen", "crankshaft "), ("kurbelwelle", "crankshaft "), ("nockenwellen", "camshaft "),
    ("nockenwelle", "camshaft "), ("einspritzventil", "injection valve "), ("einspritzung", "injection "),
    ("injektoren", "injectors "), ("injektor", "injector "), ("gluehkerze", "glow plug "),
    ("gluehsteuergeraet", "glow control unit "), ("glühsteuergerät", "glow control unit "),
    ("zuendspule", "ignition coil "), ("zündspule", "ignition coil "), ("zuendung", "ignition "),
    ("zündung", "ignition "), ("verbrennungsaussetzer", "misfire "), ("aussetzererkennung", "misfire detection "),
    ("aussetzerkennung", "misfire detection "), ("zylindergleichstellung", "cylinder balancing "),
    ("zylinder", "cylinder "), ("laufruheregler", "smooth running control "),
    ("nullmengenadaption", "zero fuel quantity adaptation "), ("gemischadaption", "mixture adaptation "),
    ("adaption", "adaptation "), ("trimmregelung", "trim control "), ("regelabweichung", "control deviation "),
    ("regelung", "control "), ("ansteuerspannung", "drive voltage "), ("ansteuerung", "control "),
    ("steuergeraet", "control unit "), ("steuergerät", "control unit "), ("steuerung", "control "),
    ("ueberwachung", "monitoring "), ("überwachung", "monitoring "), ("plausibilitaet", "plausibility "),
    ("plausibilität", "plausibility "), ("unplausibel", "implausible "), ("kurzschluss", "short circuit "),
    ("leitungsunterbrechung", "open circuit "), ("unterbrechung", "open circuit "), ("leitung", "wiring "),
    ("versorgungsspannung", "supply voltage "), ("speisespannung", "supply voltage "),
    ("spannungsversorgung", "power supply "), ("batteriespannung", "battery voltage "),
    ("unterspannung", "undervoltage "), ("ueberspannung", "overvoltage "), ("spannung", "voltage "),
    ("batterie", "battery "), ("bordnetz", "on-board electrical system "), ("generator", "alternator "),
    ("stromregelung", "current control "), ("pumpstrom", "pump current "), ("elektrischer", "electrical "),
    ("elektrische", "electrical "), ("elektrisch", "electrical "), ("elektroluefter", "electric fan "),
    ("elektrolüfter", "electric fan "), ("sensor", "sensor "), ("geber", "sensor "), ("fuehler", "sensor "),
    ("steller", "actuator "), ("stellmotor", "servo motor "), ("ventil", "valve "), ("relais", "relay "),
    ("heizung", "heater "), ("zuheizer", "auxiliary heater "), ("temperatur", "temperature "),
    ("druck", "pressure "), ("drehzahl", "speed "), ("drehmoment", "torque "), ("drehrate", "yaw rate "),
    ("geschwindigkeit", "speed "), ("fahrzeug", "vehicle "), ("raddrehzahl", "wheel speed "),
    ("lenkwinkel", "steering angle "), ("lenkradwinkel", "steering wheel angle "), ("lenkrad", "steering wheel "),
    ("fahrpedal", "accelerator pedal "), ("bremslicht", "brake light "), ("bremse", "brake "),
    ("getriebedaten", "transmission data "), ("getriebe", "transmission "), ("kupplung", "clutch "),
    ("motorlager", "engine mount "), ("motor", "engine "), ("modul", "module "), ("schalter", "switch "),
    ("schnittstelle", "interface "), ("kommunikation", "communication "), ("bedienung", "operation "),
    ("diagnoserückmeldung", "diagnostic feedback "), ("diagnosemodus", "diagnostic mode "),
    ("diagnose", "diagnosis "), ("selbsttest", "self-test "), ("codierung", "coding "),
    ("inbetriebnahme", "commissioning "), ("abschaltung", "shutdown "), ("ausfall", "failure "),
    ("ausgang", "output "), ("auswertung", "evaluation "), ("funktion", "function "), ("riemen", "belt "),
    ("verdichter", "compressor "), ("turbine", "turbine "), ("bypassklappe", "bypass flap "),
    ("bypassventil", "bypass valve "), ("kontrollleuchte", "warning lamp "), ("kuehlerjalousie", "radiator shutter "),
    ("klimaleistung", "A/C power "), ("klemme", "terminal "), ("hauptrelais", "main relay "),
    ("anlasssperr", "starter lockout "), ("starter", "starter "), ("potenziometer", "potentiometer "),
    ("potentiometer", "potentiometer "), ("hallimpulse", "Hall pulses "), ("bezugsmarke", "reference mark "),
    ("mengenregel", "quantity control "), ("mengengeregelt", "quantity controlled "),
    ("druckgeregelt", "pressure controlled "), ("sicherung", "fuse "), ("pumpe", "pump "),
    ("luefter", "fan "), ("lüfter", "fan "), ("lager", "mount "), ("licht", "light "),
    ("energiesparmode", "energy saving mode "), ("energieverbrauchsmessung", "energy consumption measurement "),
    ("fehlerort", "fault location "), ("fehlerhaft", "faulty "), ("unbekannter", "unknown "),
    ("ungueltig", "invalid "), ("mechanischer", "mechanical "), ("thermischer", "thermal "),
    ("virtuelle", "virtual "), ("fahrgeschwindigkeitssignal", "vehicle speed signal "),
    ("multifunktionslenkrad", "multifunction steering wheel "), ("anschlag", "stop "),
    ("unterbrechung", "open circuit "), ("oel", "oil "), ("öl", "oil "), ("luft", "air "),
    ("niere", "kidney grille "), ("intelligenter", "intelligent "), ("magnet", "solenoid "), ("busfehler", "bus fault "), ("analogwerterfassung", "analog value acquisition "), ("notluft", "emergency air "),
]
_TRANS = str.maketrans({"ä": "ae", "ö": "oe", "ü": "ue", "ß": "ss", "Ä": "ae", "Ö": "oe", "Ü": "ue"})
_STEMS_SORTED = sorted(((k.translate(_TRANS), v) for k, v in STEMS), key=lambda p: -len(p[0]))


def _split_compound(low):
    """Left-to-right scan: longest known word part at each position."""
    i, parts, covered = 0, [], 0
    while i < len(low):
        for stem, en in _STEMS_SORTED:
            if low.startswith(stem, i):
                parts.append(en)
                i += len(stem)
                covered += len(stem)
                break
        else:
            parts.append(low[i])
            i += 1
    if covered < 0.6 * len(low):
        return None
    return "".join(parts)


def rough_english(text):
    """Very rough word-by-word English for BMW's German fault texts."""
    import re
    out = []
    for tok in re.split(r"([^A-Za-zÄÖÜäöüß]+)", text):
        low = tok.lower().translate(_TRANS)
        if not low.isalpha():
            out.append(tok)
        elif low in WORDS:
            out.append(WORDS[low])
        elif len(low) >= 5:
            got = _split_compound(low)
            out.append(re.sub(r"\s+", " ", got).strip() if got else tok)
        else:
            out.append(tok)
    s = re.sub(r"\s+", " ", "".join(out)).strip()
    return s[:1].upper() + s[1:] if s else s



def hx(b):
    return " ".join(f"{x:02X}" for x in b)


def wait(seconds):
    end = time.perf_counter() + seconds
    while time.perf_counter() < end:
        pass


def app_dir():
    base = sys.executable if getattr(sys, "frozen", False) else os.path.abspath(__file__)
    return os.path.dirname(base)


def data_path():
    for base in (getattr(sys, "_MEIPASS", None), app_dir()):
        if base:
            p = os.path.join(base, "e60_data.db")
            if os.path.exists(p):
                return p
    return None


def clean(text, raw):
    return re.sub(rf"^\s*{raw}\s*[-:]?\s*", "", text or "", flags=re.I).strip()


class FaultDB:
    """Fault descriptions for the BMW E60, from the bundled e60_data.db."""

    def __init__(self):
        self.lock = threading.Lock()
        self.con = None
        path = data_path()
        if path:
            try:
                self.con = sqlite3.connect(f"file:{path}?mode=ro", uri=True, check_same_thread=False)
            except Exception:
                self.con = None

    def q(self, sql, args=()):
        if not self.con:
            return []
        with self.lock:
            return self.con.execute(sql, args).fetchall()

    def addresses(self):
        return [(a, n) for a, n, _ in self.q("select addr, min(name), count(*) from ecu group by addr order by addr")]

    def variants(self, addr):
        return self.q("select sgbd, name from ecu where addr=? order by sgbd", (addr,))

    def one(self, sgbd, code):
        rows = self.q("select de, en from dtc where sgbd=? and code=?", (sgbd, code))
        return rows[0] if rows else None

    def many(self, addr, code):
        """All different meanings of this code across the variants at this address."""
        rows = self.q(
            "select e.sgbd, d.de, d.en from dtc d join ecu e on e.sgbd=d.sgbd where e.addr=? and d.code=?",
            (addr, code),
        )
        groups = {}
        for sg, de, en in rows:
            key = clean(en or de, code)
            groups.setdefault(key, [de, en, []])[2].append(sg)
        return sorted(groups.values(), key=lambda g: -len(g[2]))

    def by_hwnr(self, addr, numbers):
        found = set()
        for n in numbers:
            for (sg,) in self.q("select h.sgbd from hwnr h join ecu e on e.sgbd=h.sgbd where h.hwnr=? and e.addr=?", (n, addr)):
                found.add(sg)
        return found


def describe(de, en, raw):
    """-> (english text, is_rough_translation, original german or '')"""
    if en:
        return clean(en, raw), False, ""
    german = clean(de, raw)
    rough = rough_english(german)
    if rough.lower() == german.lower():  # nothing to translate (e.g. technical names)
        return german, False, ""
    return rough, True, german


class FakeSerial:
    """Pretends to be a car so you can try the program without one."""

    PRESENT = {
        0x00: b"DEMO KGM 0000001", 0x12: b"DEMO DME 0000002", 0x18: b"DEMO EGS 0000003",
        0x29: b"DEMO DSC 0000004", 0x40: b"DEMO CAS 0000005", 0x60: b"DEMO KOMBI 000006",
        0x78: b"DEMO IHKA 0000007",
    }
    FAULTS = {
        0x12: [(0x27, 0x12, 0x2F), (0x27, 0x18, 0x2F), (0x27, 0x45, 0x2F)],
        0x29: [(0x5D, 0x8C, 0x2F)],
        0x40: [(0x93, 0x04, 0x2F)],
    }

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

    def request(self, target, data, timeout=1.5):
        self.send(self.frame(target, data))
        for _ in range(20):
            r = self.recv(timeout)
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
        r = self.request(target, [0x81], timeout=1.0)
        return bool(r) and r[0] == 0xC1

    def stop(self, target):
        try:
            self.request(target, [0x82], timeout=0.5)
        except Exception:
            pass


def ascii_part(b):
    return "".join(chr(x) if 32 <= x < 127 else "." for x in b)


BG = "#14151a"
PANEL = "#1d1f26"
FIELD = "#2a2d37"
FG = "#e6e8ee"
MUTED = "#8b90a0"
ACCENT = "#1c69d4"


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
        self.geometry("780x740")
        self.minsize(680, 560)
        self.k = None
        self.busy = False
        self.cancel = False
        self.last_faults = []
        self.q = queue.Queue()
        self.db = FaultDB()
        self.logfile = os.path.join(os.path.expanduser("~"), "e60_log.txt")
        self.style_ui()

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

        ctl = ttk.Frame(self, padding=(14, 12, 14, 0))
        ctl.pack(fill="x")
        ttk.Label(ctl, text="PORT", style="Muted.TLabel").grid(row=0, column=0, sticky="w")
        self.port = ttk.Combobox(ctl, width=16, state="readonly")
        self.port.grid(row=1, column=0)
        ttk.Button(ctl, text="↻", width=3, command=self.refresh).grid(row=1, column=1, padx=4)
        self.btn = ttk.Button(ctl, text="Open port", style="Accent.TButton", command=self.toggle)
        self.btn.grid(row=1, column=2, padx=(4, 0))

        sel = ttk.Frame(self, padding=(14, 8, 14, 0))
        sel.pack(fill="x")
        ttk.Label(sel, text="MODULE", style="Muted.TLabel").grid(row=0, column=0, sticky="w")
        ttk.Label(sel, text="VARIANT  (pick the one for your engine / car)", style="Muted.TLabel").grid(row=0, column=1, sticky="w", padx=(14, 0))
        self.mod = ttk.Combobox(sel, width=34, state="readonly")
        self.mod.grid(row=1, column=0)
        self.var = ttk.Combobox(sel, width=58, state="readonly")
        self.var.grid(row=1, column=1, padx=(14, 0), sticky="we")
        sel.columnconfigure(1, weight=1)
        self.mod.bind("<<ComboboxSelected>>", lambda e: self.fill_variants())
        addrs = self.db.addresses()
        if not addrs:
            addrs = [(a, ADDR_NAMES.get(a, "Module")) for a in QUICK]
        self.mod["values"] = [f"{a:02X}  {ADDR_NAMES.get(a, n or 'Module')[:40]}" for a, n in addrs]
        self.mod.set("12  " + ADDR_NAMES[0x12])
        self.fill_variants()

        acts = ttk.Frame(self, padding=(14, 10))
        acts.pack(fill="x")
        ttk.Button(acts, text="Quick scan", style="Accent.TButton", command=lambda: self.run(self.scan_quick, scan=True)).pack(side="left")
        ttk.Button(acts, text="Full scan", command=lambda: self.run(self.scan_full, scan=True)).pack(side="left", padx=8)
        ttk.Button(acts, text="Identify", command=lambda: self.run(self.ident)).pack(side="left")
        ttk.Button(acts, text="Read faults", style="Accent.TButton", command=lambda: self.run(self.faults)).pack(side="left", padx=8)
        ttk.Button(acts, text="Stop", command=self.stop_scan).pack(side="left")
        ttk.Button(acts, text="Copy this tab", command=self.copy).pack(side="right")
        ttk.Button(acts, text="Look up online", command=self.lookup).pack(side="right", padx=8)

        self.tabs = ttk.Notebook(self)
        self.tabs.pack(fill="both", expand=True, padx=14, pady=(4, 8))
        res_frame = ttk.Frame(self.tabs)
        log_frame = ttk.Frame(self.tabs)
        self.tabs.add(res_frame, text="  Results  ")
        self.tabs.add(log_frame, text="  Technical log  ")

        self.res = tk.Text(
            res_frame, font=("Segoe UI", 11), state="disabled", bg="#181a20", fg=FG, relief="flat",
            padx=20, pady=14, wrap="word", cursor="arrow", spacing1=2, spacing3=2,
        )
        rsb = ttk.Scrollbar(res_frame, command=self.res.yview)
        self.res.config(yscrollcommand=rsb.set)
        rsb.pack(side="right", fill="y")
        self.res.pack(side="left", fill="both", expand=True)
        r = self.res
        r.tag_config("h1", font=("Segoe UI", 17, "bold"), foreground="#ffffff", spacing1=2, spacing3=2)
        r.tag_config("sub", font=("Segoe UI", 10), foreground=MUTED, spacing3=8)
        r.tag_config("chip", font=("Consolas", 12, "bold"), foreground="#14151a", background="#ffb454", spacing1=16)
        r.tag_config("meaning", font=("Segoe UI", 12, "bold"), foreground="#ffffff", spacing1=16)
        r.tag_config("orig", font=("Segoe UI", 10), foreground=MUTED, lmargin1=18, lmargin2=18, spacing3=2)
        r.tag_config("item", font=("Segoe UI", 11), foreground=FG, lmargin1=18, lmargin2=34, spacing3=2)
        r.tag_config("ok", font=("Segoe UI", 13, "bold"), foreground="#4cd964", spacing1=10)
        r.tag_config("bad", font=("Segoe UI", 11, "bold"), foreground="#ff6b6b", spacing1=6)
        r.tag_config("good", font=("Segoe UI", 12, "bold"), foreground="#4cd964")
        r.tag_config("body", font=("Segoe UI", 11), foreground=FG, spacing3=4)
        r.tag_config("hint", font=("Segoe UI", 10), foreground=MUTED, spacing1=14)

        self.text = tk.Text(
            log_frame, font=("Consolas", 9), state="disabled", bg="#0f1014", fg=FG,
            relief="flat", padx=10, pady=8, wrap="word", insertbackground=FG,
        )
        sb = ttk.Scrollbar(log_frame, command=self.text.yview)
        self.text.config(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        self.text.pack(side="left", fill="both", expand=True)
        self.text.tag_config("tx", foreground="#7f8598")
        self.text.tag_config("rx", foreground="#8fd19e")
        self.text.tag_config("head", foreground="#6aa9ff", font=("Consolas", 9, "bold"))
        self.text.tag_config("good", foreground="#4cd964", font=("Consolas", 9, "bold"))
        self.text.tag_config("bad", foreground="#ff6b6b")
        self.text.tag_config("fault", foreground="#ffb454", font=("Consolas", 9, "bold"))

        self.refresh()
        self.render_welcome()
        self.log(f"Technical log, also saved to {self.logfile}")
        if not self.db.con:
            self.log("ERROR: fault database e60_data.db not found - only fault numbers will be shown.")
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
        st.configure("TNotebook", background=PANEL, borderwidth=0)
        st.configure("TNotebook.Tab", background="#2f323d", foreground=MUTED, padding=(16, 8), borderwidth=0)
        st.map("TNotebook.Tab", background=[("selected", ACCENT)], foreground=[("selected", "white")])
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
        if body.startswith(("TX", "DE:")):
            return "tx"
        if body.startswith("RX"):
            return "rx"
        if body.startswith("---"):
            return "head"
        if body.startswith("FAULT"):
            return "fault"
        if body.startswith("EN:"):
            return "desc"
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
                if item[0] == "status":
                    self.status.set(item[1])
                elif item[0] == "variant":
                    self.set_variant(item[1])
                elif item[0] == "show":
                    try:
                        self.render(item[1], item[2])
                    except Exception as e:
                        self.text.config(state="normal")
                        self.text.insert("end", f"ERROR drawing results: {e}\n")
                        self.text.config(state="disabled")
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
        box = self.res if self.tabs.index(self.tabs.select()) == 0 else self.text
        self.clipboard_clear()
        self.clipboard_append(box.get("1.0", "end"))

    # ---- port / selection ----
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
            raise ValueError("Pick a module from the Module list.")

    def fill_variants(self):
        try:
            addr = self.target()
        except ValueError:
            return
        vs = self.db.variants(addr)
        values = [AUTO] + [f"{sg}  -  {name}" for sg, name in vs]
        self.var["values"] = values
        self.var.set(values[1] if len(vs) == 1 else AUTO)

    def set_variant(self, sgbd):
        for v in self.var["values"]:
            if v.startswith(sgbd + "  -  "):
                self.var.set(v)
                return

    def current_sgbd(self):
        v = self.var.get()
        return None if (not v or v.startswith("Auto")) else v.split()[0]

    def addr_name(self, a):
        return ADDR_NAMES.get(a) or next((n for x, n in self.db.addresses() if x == a), "Module")

    def stop_scan(self):
        self.cancel = True

    def run(self, fn, scan=False):
        if not self.k:
            return messagebox.showinfo("Port closed", "Press Open port first.")
        if self.busy:
            return
        try:
            ctx = None if scan else (self.target(), self.current_sgbd(), self.mod.get())
        except ValueError as e:
            return messagebox.showinfo("Module", str(e))
        self.busy = True
        self.cancel = False

        def work():
            self.q.put(("status", "Working…"))
            try:
                fn(ctx)
            except Exception as e:
                self.log(f"ERROR: {e}")
            finally:
                self.busy = False
                self.q.put(("status", "Ready"))

        threading.Thread(target=work, daemon=True).start()

    # ---- actions ----
    def show(self, kind, payload):
        self.q.put(("show", kind, payload))

    def scan_quick(self, ctx):
        self.scan(QUICK)

    def scan_full(self, ctx):
        self.scan([a for a, _ in self.db.addresses()] or QUICK)

    def scan(self, addrs):
        total = len(addrs)
        self.log(f"--- Scan: asking {total} modules to answer ---")
        found = []
        self.show("scan", dict(found=[], done=False, total=total, tried=0))
        for i, a in enumerate(addrs, 1):
            if self.cancel:
                self.log("Scan stopped.")
                return self.show("scan", dict(found=list(found), done=True, stopped=True, total=total, tried=i - 1))
            self.q.put(("status", f"Scanning {a:02X} {self.addr_name(a)} ({i} of {total}) …"))
            if self.k.start(a):
                found.append((a, self.addr_name(a)))
                self.log(f">>> {a:02X}  {self.addr_name(a)}  ANSWERED")
                self.k.stop(a)
                self.show("scan", dict(found=list(found), done=False, total=total, tried=i))
            time.sleep(0.3)
        self.log("--- Scan done ---")
        self.show("scan", dict(found=found, done=True, total=total, tried=total))

    def no_answer(self, name):
        self.log("No answer from module (see TX/RX lines above)")
        self.show("message", dict(
            title=name, level="bad",
            text="This module did not answer.\nCheck that the cable is plugged in at both ends, the ignition is on, "
                 "and that your car has this module. The Technical log tab shows what was sent.",
        ))

    def ident(self, ctx):
        t, sgbd, name = ctx
        self.log(f"--- Identify module {t:02X} ---")
        if not self.k.start(t):
            return self.no_answer(name)
        r = self.k.request(t, [0x1A, 0x80])
        if r and r[0] == 0x5A:
            text = ascii_part(r[2:])
            self.log("Identification text: " + text)
            hexs = "".join(f"{x:02X}" for x in r[2:])
            nums = set(re.findall(r"\d{7}", text)) | set(re.findall(r"(?=(\d{7}))", hexs))
            match = self.db.by_hwnr(t, nums)
            sg = next(iter(match)) if len(match) == 1 else None
            if sg:
                self.log(f"Part number matches variant {sg} - selected it for you.")
                self.q.put(("variant", sg))
            self.show("ident", dict(module=name, text=text, match=sg))
        else:
            self.show("message", dict(title=name, level="bad", text=self.explain(r)))
        self.k.stop(t)

    def faults(self, ctx):
        t, sgbd, name = ctx
        self.log(f"--- Fault memory of module {name} ---")
        if not self.k.start(t):
            return self.no_answer(name)
        r = self.k.request(t, [0x18, 0x00, 0xFF, 0x00])
        if r and r[0] == 0x58:
            body = r[2:]
            items = []
            for i in range(0, len(body) - 2, 3):
                hi, lo, st = body[i], body[i + 1], body[i + 2]
                items.append(self.explain_code(t, sgbd, f"{hi:02X}{lo:02X}", st))
            self.last_faults = [(name, it["code"]) for it in items]
            path = self.save_report(name, sgbd, items)
            self.show("faults", dict(module=name, sgbd=sgbd, items=items, path=path))
        else:
            self.show("message", dict(title=name, level="bad", text=self.explain(r)))
        self.k.stop(t)

    def explain_code(self, addr, sgbd, raw, st):
        """Looks up one fault code; returns a dict used by the result cards and the report."""
        self.log(f"FAULT {raw}  status {st:02X}")
        item = {"code": raw, "st": st, "groups": [], "note": "", "more": 0}
        if not self.db.con:
            item["note"] = "No fault database loaded."
            return item
        if sgbd:
            row = self.db.one(sgbd, raw)
            if not row:
                item["note"] = "Not in the database for this variant. Is the variant right?"
                return item
            en, rough, de = describe(row[0], row[1], raw)
            item["groups"].append({"en": en, "rough": rough, "de": de, "variants": ""})
            return item
        groups = self.db.many(addr, raw)
        if not groups:
            item["note"] = "Not found in any variant of this module."
            return item
        for de, en, sgs in groups[:4]:
            en_t, rough, de_t = describe(de, en, raw)
            who = ", ".join(sgs[:3]) + (f" +{len(sgs) - 3} more" if len(sgs) > 3 else "")
            item["groups"].append({"en": en_t, "rough": rough, "de": de_t, "variants": who})
        item["more"] = max(0, len(groups) - 4)
        return item

    @staticmethod
    def item_text(it):
        if not it["groups"]:
            return it["note"]
        return " / ".join(g["en"] + (f"  [DE: {g['de']}]" if g["de"] else "") for g in it["groups"][:2])

    def save_report(self, module, sgbd, items):
        folder = os.path.join(os.path.expanduser("~"), "Documents")
        if not os.path.isdir(folder):
            folder = os.path.expanduser("~")
        path = os.path.join(folder, "E60_fault_report.txt")
        try:
            with open(path, "a", encoding="utf-8") as f:
                f.write(f"\n=== {time.strftime('%Y-%m-%d %H:%M')}  {module}  variant: {sgbd or 'auto'} ===\n")
                if not items:
                    f.write("No stored faults\n")
                for it in items:
                    f.write(f"{it['code']}  {self.item_text(it)}\n")
            return path
        except Exception as e:
            self.log(f"ERROR: could not save report: {e}")
            return None

    # ---- result cards ----
    def res_clear(self):
        self.res.config(state="normal")
        self.res.delete("1.0", "end")
        self.res.config(state="disabled")

    def res_add(self, text, *tags):
        self.res.config(state="normal")
        self.res.insert("end", text, tags)
        self.res.config(state="disabled")

    def render(self, kind, payload):
        getattr(self, "render_" + kind)(payload)
        self.tabs.select(0)

    def render_welcome(self):
        self.res_clear()
        self.res_add("Welcome\n", "h1")
        self.res_add("Read the fault memory of your BMW E60 and see what each fault means.\n", "sub")
        for i, s in enumerate([
            "Plug the cable into the car and the PC, and turn the ignition on.",
            "Choose the port above and press Open port.",
            "Press Quick scan to see which modules answer.",
            "Pick a module and your variant, then press Read faults.",
        ], 1):
            self.res_add(f"{i}.  {s}\n", "item")
        self.res_add("\nNo car handy? Choose 'Demo (no car)' as the port to try the program.\n", "hint")
        if not self.db.con:
            self.res_add("\nThe fault database (e60_data.db) was not found, so only fault numbers can be shown.\n", "bad")

    def render_message(self, p):
        self.res_clear()
        self.res_add(p["title"] + "\n", "h1")
        self.res_add(p["text"] + "\n", "bad" if p.get("level") == "bad" else "body")

    def render_scan(self, p):
        self.res_clear()
        self.res_add("Modules\n", "h1")
        if p["done"]:
            state = "Scan stopped" if p.get("stopped") else "Scan complete"
        else:
            state = f"Scanning…  {p['tried']} of {p['total']}"
        self.res_add(f"{state}   ·   {len(p['found'])} answered\n", "sub")
        for a, name in p["found"]:
            self.res_add("●  ", "good")
            self.res_add(f"{a:02X}    {name}\n", "body")
        if p["done"] and p["found"]:
            self.res_add("\nChoose a module in the Module list above and press Read faults.\n", "hint")
        elif p["done"]:
            self.res_add(
                "\nNothing answered. Check that the cable is plugged in at both ends, the ignition is on, "
                "the cable switch is on K-line and the right port is open.\n", "bad")

    def render_ident(self, p):
        self.res_clear()
        self.res_add("Identification\n", "h1")
        self.res_add(p["module"] + "\n", "sub")
        self.res_add(p["text"] + "\n", "meaning")
        if p.get("match"):
            self.res_add(f"\nThe part number matches variant {p['match']}. It has been selected for you.\n", "good")
        else:
            self.res_add("\nThis text helps to tell which variant your control unit is.\n", "hint")

    def render_faults(self, p):
        self.res_clear()
        items = p["items"]
        n = len(items)
        self.res_add(p["module"] + "\n", "h1")
        variant = f"Variant: {p['sgbd']}" if p["sgbd"] else "Variant: not chosen, showing every possibility"
        self.res_add(f"{variant}   ·   {n} fault{'s' if n != 1 else ''} stored\n", "sub")
        if not n:
            self.res_add("✓  No stored faults\n", "ok")
        for it in items:
            self.res_add(f" {it['code']} ", "chip")
            groups = it["groups"]
            if not groups:
                self.res_add("   " + it["note"] + "\n", "meaning")
            elif len(groups) == 1:
                g = groups[0]
                self.res_add("   " + g["en"] + "\n", "meaning")
                if g["de"]:
                    self.res_add(f"German original: {g['de']}   ·   translated automatically\n", "orig")
                if g["variants"]:
                    self.res_add(f"Variants: {g['variants']}\n", "orig")
            else:
                self.res_add("   Meaning depends on the variant\n", "meaning")
                for g in groups:
                    mark = "  (translated automatically)" if g["rough"] else ""
                    self.res_add(f"•  {g['en']}{mark}   [{g['variants']}]\n", "item")
                if it["more"]:
                    self.res_add(f"…and {it['more']} more possibilities\n", "orig")
        if p.get("path"):
            self.res_add(f"\nSaved to {p['path']}\n", "hint")
        if any(len(it["groups"]) > 1 for it in items):
            self.res_add("Pick your variant in the Variant list and press Read faults again for one clear answer.\n", "hint")

    def lookup(self):
        if not self.last_faults:
            return messagebox.showinfo("Nothing to look up", "Press Read faults first.")
        for name, raw in self.last_faults[:5]:
            module = name.split(" ", 1)[-1]
            q = quote_plus(f"BMW E60 {module} fault code {raw}")
            webbrowser.open_new_tab("https://www.google.com/search?q=" + q)

    def explain(self, r):
        if r is None:
            msg = "The module did not reply to the request."
        elif r[0] == 0x7F and len(r) >= 3:
            msg = f"The module refused the request: {NRC.get(r[2], hex(r[2]))}."
        else:
            msg = "Unexpected reply: " + hx(r)
        self.log(msg)
        return msg

    def on_close(self):
        if self.k:
            self.k.close()
        self.destroy()


if __name__ == "__main__":
    App().mainloop()
