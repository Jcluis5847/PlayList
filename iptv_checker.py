# -*- coding: cp1252 -*-
"""IPTV CHECKER - verificador de listas M3U con comprobación real de reproducción.

Requisitos:
    py -m pip install python-vlc
    + VLC de escritorio instalado (misma arquitectura que Python: 64 bits con 64 bits)
"""
import ctypes
import queue
import re
import sys
import threading
import time
import tkinter as tk
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from tkinter import filedialog, messagebox, ttk

try:
    import vlc
    VLC_ERROR = None
except Exception as exc:  # ImportError, o libvlc no encontrada
    vlc = None
    VLC_ERROR = f"{type(exc).__name__}: {exc}"

APP_TITLE = "IPTV CHECKER"
OUTPUT_NAME = "CANALES_FUNCIONALES.m3u"

STARTUP_TIMEOUT = 20      # segundos máximos esperando el primer cuadro / inicio
AUDIO_GRACE = 4           # segundos en Playing sin video para considerar "solo audio"
MIN_FPS = 1               # cuadros nuevos por segundo mínimos para considerar el flujo estable
MAX_WORKERS = 32
MAX_LISTS = 15            # casilleros de listas en la ventana "+"
VIDEO_TRACK_TYPE = 1      # libvlc_track_video

URL_RE = re.compile(r"^(https?|rtsp|rtmps?|udp|rtp|mms|mmsh)://", re.IGNORECASE)
RES_SUFFIX_RE = re.compile(r"\s*\((?:\d{3,4}[Pp]|[2348][Kk])\)\s*$")
RES_ORDER = ["8K", "4K", "2K", "1080P", "720P", "576P", "540P", "480P"]


# ----------------------------------------------------------------------------
# M3U: descarga, parseo y escritura (sin dependencias de UI)
# ----------------------------------------------------------------------------
@dataclass
class Channel:
    name: str
    url: str
    meta: list = field(default_factory=list)
    resolution: str = ""


def download_m3u(source):
    source = source.strip().strip('"')
    if source.lower().startswith(("http://", "https://")):
        request = urllib.request.Request(
            source, headers={"User-Agent": "Mozilla/5.0 IPTV-Checker/1.0"}
        )
        with urllib.request.urlopen(request, timeout=25) as response:
            data = response.read()
        return data.decode("utf-8-sig", errors="replace")

    with open(source, "r", encoding="utf-8-sig", errors="replace") as f:
        return f.read()


def _extinf_name(line):
    """Nombre = texto tras la primera coma que no está dentro de comillas."""
    in_quotes = False
    for i, ch in enumerate(line):
        if ch == '"':
            in_quotes = not in_quotes
        elif ch == "," and not in_quotes:
            return line[i + 1:].strip() or None
    return None


def parse_m3u(text):
    """Devuelve (header, [Channel, ...]). El header (#EXTM3U ...) se conserva aparte."""
    header = "#EXTM3U"
    channels = []
    pending = []
    current_name = None

    for line in (ln.strip() for ln in text.splitlines()):
        if not line:
            continue

        if line.startswith("#"):
            upper = line.upper()
            if upper.startswith("#EXTM3U"):
                header = line
                continue
            if upper.startswith("#EXTINF:"):
                pending = [m for m in pending if not m.upper().startswith("#EXTINF:")]
                current_name = _extinf_name(line)
            pending.append(line)
            continue

        if URL_RE.match(line):
            channels.append(
                Channel(current_name or f"Canal {len(channels) + 1}", line, pending)
            )

        # Con URL válida o no, los metadatos pendientes no deben "filtrarse" al siguiente.
        pending = []
        current_name = None

    return header, channels


def dedupe_channels(channels):
    seen = set()
    unique = []
    for ch in channels:
        if ch.url in seen:
            continue
        seen.add(ch.url)
        unique.append(ch)
    return unique, len(channels) - len(unique)


def classify_resolution(width, height):
    """Etiqueta de resolución a partir del tamaño del video: 720P, 1080P, 2K, 4K..."""
    if width <= 0 or height <= 0:
        return ""
    if width >= 7000 or height >= 4000:
        return "8K"
    if width >= 3600 or height >= 2000:
        return "4K"
    if width >= 2400 or height >= 1300:
        return "2K"
    if width >= 1800 or height >= 1000:
        return "1080P"
    if width >= 1200 or height >= 680:
        return "720P"
    if height >= 576:
        return "576P"
    if height >= 480:
        return "480P"
    return f"{height}P"


def with_resolution(meta_lines, name, resolution):
    """Copia de las líneas de metadatos con ' (720P)' al final del título del #EXTINF."""
    if not resolution:
        return list(meta_lines)

    out = []
    done = False
    for line in meta_lines:
        if not done and line.upper().startswith("#EXTINF:"):
            base = RES_SUFFIX_RE.sub("", line).rstrip()
            if _extinf_name(base) is None:  # sin título: se lo agregamos
                base = base + name if base.endswith(",") else f"{base},{name}"
            line = f"{base} ({resolution})"
            done = True
        out.append(line)

    if not done:
        out.insert(0, f"#EXTINF:-1,{name} ({resolution})")
    return out


def fmt_time(seconds):
    seconds = int(max(0, seconds))
    h, rem = divmod(seconds, 3600)
    m, s = divmod(rem, 60)
    return f"{h:02d}:{m:02d}:{s:02d}"


def short(text, limit=60):
    return text if len(text) <= limit else text[: limit - 1] + "…"


# ----------------------------------------------------------------------------
# VLC: salida de video a memoria, ventana embebida y lectura de resolución
# ----------------------------------------------------------------------------
class FrameSink:
    """Recibe los cuadros en memoria (modo silencio): sin ventana, un sink por reproductor."""

    def __init__(self, width=320, height=180):
        self.width = width
        self.height = height
        self.pitch = width * 4
        self.buffer = ctypes.create_string_buffer(self.pitch * height)
        self.frames = 0

        @vlc.CallbackDecorators.VideoLockCb
        def lock(opaque, planes):
            planes[0] = ctypes.cast(self.buffer, ctypes.c_void_p)
            return None

        @vlc.CallbackDecorators.VideoUnlockCb
        def unlock(opaque, picture, planes):
            pass

        @vlc.CallbackDecorators.VideoDisplayCb
        def display(opaque, picture):
            self.frames += 1

        # Referencias vivas durante toda la vida del sink (y del reproductor).
        self._callbacks = (lock, unlock, display)

    def attach(self, player):
        player.video_set_callbacks(*self._callbacks, None)
        player.video_set_format("RV32", self.width, self.height, self.pitch)

    def reset(self):
        self.frames = 0


def embed_player(player, wid):
    if sys.platform.startswith("win"):
        player.set_hwnd(wid)
    elif sys.platform == "darwin":
        player.set_nsobject(wid)
    else:
        player.set_xwindow(wid)


def get_video_resolution(player, media, ignore_size=None):
    """(ancho, alto) del video de ORIGEN, o (0, 0) si no se pudo leer.

    1) Pistas del stream (media.tracks_get): tamaño real de origen, aunque el video
       se esté escalando a 320x180 en memoria.
    2) player.video_get_size como respaldo (se descarta si coincide con ignore_size,
       que es el tamaño forzado del modo silencio).
    """
    try:
        tracks = media.tracks_get()
        for item in (tracks or []):
            track = item.contents if hasattr(item, "contents") else item
            ttype = getattr(track.type, "value", track.type)
            if ttype != VIDEO_TRACK_TYPE:
                continue
            video = getattr(track, "video", None)
            if video is None:
                video = track.u.video
            video = video.contents if hasattr(video, "contents") else video
            width, height = int(video.width), int(video.height)
            if width > 0 and height > 0:
                return width, height
    except Exception:
        pass

    try:
        width, height = player.video_get_size(0)
        if width > 0 and height > 0 and (width, height) != ignore_size:
            return width, height
    except Exception:
        pass

    return 0, 0


# ----------------------------------------------------------------------------
# Aplicación
# ----------------------------------------------------------------------------
class IPTVChecker:

    def __init__(self, root):
        self.root = root
        self.root.title(APP_TITLE)
        self.root.geometry("880x830")
        self.root.minsize(780, 680)

        self.events = queue.Queue()
        self.stop_event = threading.Event()
        self.worker = None
        self.running = False

        # Estado (solo lo modifica el hilo de la UI, a partir de eventos)
        self.channels = []
        self.header = "#EXTM3U"
        self.good = {}          # índice -> Channel
        self.errors = []        # (nombre, motivo)
        self.active = {}        # índice -> nombre (canales en prueba ahora mismo)
        self.total = 0
        self.checked = 0
        self.dur_sum = 0.0
        self.workers_used = 1
        self.test_start = None
        self.test_end = None

        self._controls = []
        self._build_ui()
        self._build_sources_window()
        self._on_mode_change()

        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.root.after(100, self._process_events)
        self.root.after(500, self._tick_clock)

    # ------------------------------------------------------------------ UI
    def _build_ui(self):
        outer = ttk.Frame(self.root, padding=16)
        outer.pack(fill="both", expand=True)

        ttk.Label(outer, text="IPTV CHECKER", font=("Segoe UI", 20, "bold")).pack(anchor="w")
        ttk.Label(
            outer,
            text="Verificador de listas M3U con comprobación real de reproducción y resolución",
            foreground="#666",
        ).pack(anchor="w", pady=(0, 14))

        ttk.Label(
            outer,
            text="URL de la lista M3U o ruta de un archivo local (con + cargás hasta "
                 f"{MAX_LISTS} listas):",
        ).pack(anchor="w")

        url_row = ttk.Frame(outer)
        url_row.pack(fill="x", pady=(5, 2))

        # El casillero 1 de la ventana "+" es este mismo campo.
        self.url_var = tk.StringVar()
        self.source_vars = [self.url_var] + [tk.StringVar() for _ in range(MAX_LISTS - 1)]

        self.url_entry = ttk.Entry(url_row, textvariable=self.url_var)
        self.url_entry.pack(side="left", fill="x", expand=True)
        browse_btn = ttk.Button(url_row, text="Examinar…", command=lambda: self._browse_multi(0))
        browse_btn.pack(side="left", padx=(8, 0))
        self.plus_btn = ttk.Button(url_row, text="+", width=3, command=self._open_sources_window)
        self.plus_btn.pack(side="left", padx=(8, 0))

        self.sources_info = ttk.Label(outer, text="", foreground="#666", font=("Segoe UI", 8))
        self.sources_info.pack(anchor="w", pady=(0, 10))
        for var in self.source_vars:
            var.trace_add("write", lambda *_: self._update_sources_info())
        self._update_sources_info()

        # ---- Configuración de prueba
        settings = ttk.LabelFrame(outer, text="Configuración de prueba", padding=10)
        settings.pack(fill="x", pady=(0, 12))

        ttk.Label(settings, text="Tiempo por canal (segundos):").grid(row=0, column=0, sticky="w")
        self.seconds_var = tk.StringVar(value="5")
        seconds_spin = ttk.Spinbox(settings, from_=1, to=120, width=7, textvariable=self.seconds_var)
        seconds_spin.grid(row=0, column=1, padx=(8, 22), sticky="w")

        ttk.Label(settings, text="Modo:").grid(row=0, column=2, sticky="w")
        self.mode_var = tk.StringVar(value="silencio")
        radio_silent = ttk.Radiobutton(
            settings, text="Silencio (recomendado)", variable=self.mode_var,
            value="silencio", command=self._on_mode_change,
        )
        radio_silent.grid(row=0, column=3, padx=8, sticky="w")
        radio_visual = ttk.Radiobutton(
            settings, text="Visual", variable=self.mode_var,
            value="visual", command=self._on_mode_change,
        )
        radio_visual.grid(row=0, column=4, padx=8, sticky="w")

        ttk.Label(settings, text="Canales a verificar a la vez:").grid(
            row=1, column=0, sticky="w", pady=(10, 0)
        )
        self.workers_var = tk.StringVar(value="4")
        self.workers_spin = ttk.Spinbox(
            settings, from_=1, to=MAX_WORKERS, width=7, textvariable=self.workers_var
        )
        self.workers_spin.grid(row=1, column=1, padx=(8, 22), sticky="w", pady=(10, 0))

        self.workers_hint = ttk.Label(settings, text="", foreground="#666")
        self.workers_hint.grid(row=1, column=2, columnspan=3, sticky="w", pady=(10, 0))

        self.dedupe_var = tk.BooleanVar(value=True)
        dedupe_chk = ttk.Checkbutton(
            settings, text="Eliminar URLs duplicadas antes de probar", variable=self.dedupe_var
        )
        dedupe_chk.grid(row=2, column=0, columnspan=3, sticky="w", pady=(10, 0))

        self.audio_var = tk.BooleanVar(value=False)
        audio_chk = ttk.Checkbutton(
            settings, text="Aceptar canales de solo audio (radios)", variable=self.audio_var
        )
        audio_chk.grid(row=2, column=3, columnspan=2, sticky="w", pady=(10, 0))

        # Controles que se bloquean mientras corre la comprobación
        self._controls = [
            self.url_entry, browse_btn, seconds_spin, radio_silent, radio_visual,
            self.workers_spin, dedupe_chk, audio_chk,
        ]

        # ---- Botones
        actions = ttk.Frame(outer)
        actions.pack(fill="x", pady=(0, 12))

        self.start_btn = ttk.Button(actions, text="INICIAR COMPROBACIÓN", command=self.start)
        self.start_btn.pack(side="left")
        self.stop_btn = ttk.Button(actions, text="DETENER", command=self.stop, state="disabled")
        self.stop_btn.pack(side="left", padx=8)
        self.save_btn = ttk.Button(
            actions, text="GUARDAR CANALES FUNCIONALES", command=self.save, state="disabled"
        )
        self.save_btn.pack(side="right")

        # ---- Estado de la comprobación
        stats = ttk.LabelFrame(outer, text="Estado de la comprobación", padding=10)
        stats.pack(fill="x", pady=(0, 12))

        self.current_var = tk.StringVar(value="Esperando una lista…")
        ttk.Label(stats, textvariable=self.current_var, font=("Segoe UI", 10, "bold")).pack(anchor="w")

        self.progress = ttk.Progressbar(stats, maximum=100, mode="determinate")
        self.progress.pack(fill="x", pady=8)

        self.progress_var = tk.StringVar(value="0%")
        ttk.Label(stats, textvariable=self.progress_var).pack(anchor="e")

        self.count_var = tk.StringVar(value="Comprobados: 0 / 0     Funcionan: 0     Fallidos: 0")
        ttk.Label(stats, textvariable=self.count_var).pack(anchor="w", pady=(5, 0))

        time_row = ttk.Frame(stats)
        time_row.pack(fill="x", pady=(5, 0))
        self.elapsed_var = tk.StringVar(value="Tiempo transcurrido: 00:00:00")
        self.remaining_var = tk.StringVar(value="Tiempo restante: --:--:--")
        ttk.Label(time_row, textvariable=self.elapsed_var, font=("Segoe UI", 10, "bold")).pack(side="left")
        ttk.Label(time_row, textvariable=self.remaining_var, font=("Segoe UI", 10, "bold")).pack(side="right")

        # ---- Vista previa (solo modo Visual)
        self.preview = tk.Frame(outer, bg="black", height=200)
        self.preview.pack_propagate(False)

        # ---- Registro
        self.results_frame = ttk.LabelFrame(outer, text="Registro de actividad y errores", padding=8)
        self.results_frame.pack(fill="both", expand=True)

        self.log = tk.Text(
            self.results_frame, height=12, wrap="word", state="disabled", font=("Consolas", 9)
        )
        scroll = ttk.Scrollbar(self.results_frame, orient="vertical", command=self.log.yview)
        self.log.configure(yscrollcommand=scroll.set)
        self.log.pack(side="left", fill="both", expand=True)
        scroll.pack(side="right", fill="y")

        ttk.Label(
            outer,
            text=("Un canal es funcional si VLC decodifica cuadros de video de forma sostenida "
                  "durante el tiempo configurado. También se detecta su resolución."),
            foreground="#666",
            font=("Segoe UI", 8),
        ).pack(anchor="w", pady=(8, 0))

    # ------------------------------------------- Ventana "+" (varias listas)
    def _build_sources_window(self):
        win = tk.Toplevel(self.root)
        win.title(f"Listas M3U (hasta {MAX_LISTS})")
        win.transient(self.root)
        win.protocol("WM_DELETE_WINDOW", win.withdraw)
        win.withdraw()
        self.sources_win = win

        frame = ttk.Frame(win, padding=14)
        frame.pack(fill="both", expand=True)

        ttk.Label(
            frame,
            text=("Cargá las listas (URL o archivo). Al iniciar se leen todas, se combinan en "
                  "una sola y se verifican juntas."),
            foreground="#666",
        ).pack(anchor="w", pady=(0, 10))

        grid = ttk.Frame(frame)
        grid.pack(fill="x")
        grid.columnconfigure(1, weight=1)

        for i, var in enumerate(self.source_vars):
            ttk.Label(grid, text=f"{i + 1}.", width=3, anchor="e").grid(row=i, column=0, pady=2)
            entry = ttk.Entry(grid, textvariable=var, width=72)
            entry.grid(row=i, column=1, sticky="ew", padx=6, pady=2)
            btn = ttk.Button(grid, text="…", width=3, command=lambda n=i: self._browse_multi(n))
            btn.grid(row=i, column=2, pady=2)
            self._controls.extend([entry, btn])

        bottom = ttk.Frame(frame)
        bottom.pack(fill="x", pady=(14, 0))

        clear_btn = ttk.Button(bottom, text="Limpiar todas", command=self._clear_sources)
        clear_btn.pack(side="left")
        popup_start = ttk.Button(
            bottom, text="INICIAR COMPROBACIÓN", command=self._start_from_window
        )
        popup_start.pack(side="right")
        self._controls.extend([clear_btn, popup_start])

    def _open_sources_window(self):
        win = self.sources_win
        win.geometry(f"+{self.root.winfo_rootx() + 40}+{self.root.winfo_rooty() + 40}")
        win.deiconify()
        win.lift()
        win.focus_force()

    def _start_from_window(self):
        if self.start():
            self.sources_win.withdraw()

    def _clear_sources(self):
        for var in self.source_vars:
            var.set("")

    def _dialog_parent(self):
        return self.sources_win if self.sources_win.winfo_viewable() else self.root

    def _get_sources(self):
        seen = set()
        sources = []
        for var in self.source_vars:
            text = var.get().strip().strip('"')
            if text and text not in seen:
                seen.add(text)
                sources.append(text)
        return sources

    def _update_sources_info(self):
        count = len(self._get_sources())
        if count <= 1:
            text = "Listas cargadas: " + str(count) + "   (usá + para sumar más)"
        else:
            text = f"Listas cargadas: {count}   (se combinarán en una sola)"
        self.sources_info.configure(text=text)

    def _browse_multi(self, start_index):
        parent = self._dialog_parent()
        paths = filedialog.askopenfilenames(
            parent=parent,
            title="Seleccionar lista(s) M3U",
            filetypes=[("Listas M3U", "*.m3u *.m3u8"), ("Todos los archivos", "*.*")],
        )
        if not paths:
            return

        slots = [start_index] + [
            i for i, var in enumerate(self.source_vars)
            if i != start_index and not var.get().strip()
        ]
        for slot, path in zip(slots, paths):
            self.source_vars[slot].set(path)

        if len(paths) > len(slots):
            messagebox.showwarning(
                "Casilleros llenos",
                f"Solo hay {MAX_LISTS} casilleros: se ignoraron {len(paths) - len(slots)} archivo(s).",
                parent=parent,
            )

    # ------------------------------------------------------- Modo / controles
    def _on_mode_change(self):
        visual = self.mode_var.get() == "visual"
        if visual:
            self.workers_spin.configure(state="disabled")
            self.workers_hint.configure(text="En modo Visual se prueba 1 canal a la vez.")
            if not self.preview.winfo_ismapped():
                self.preview.pack(fill="x", pady=(0, 12), before=self.results_frame)
        else:
            if not self.running:
                self.workers_spin.configure(state="normal")
            self.workers_hint.configure(
                text="Más canales a la vez = más rápido, pero más CPU y red."
            )
            self.preview.pack_forget()

    def _set_controls(self, enabled):
        state = "normal" if enabled else "disabled"
        for widget in self._controls:
            widget.configure(state=state)
        if enabled:
            self._on_mode_change()  # vuelve a bloquear "a la vez" si el modo es Visual

    def _log(self, message):
        self.log.configure(state="normal")
        self.log.insert("end", f"{time.strftime('%H:%M:%S')}  {message}\n")
        self.log.see("end")
        self.log.configure(state="disabled")

    @staticmethod
    def _read_int(var, low, high):
        try:
            value = int(var.get())
        except ValueError:
            return None
        return value if low <= value <= high else None

    # ------------------------------------------------------------- Control
    def start(self):
        """Inicia la comprobación. Devuelve True si arrancó."""
        if self.running:
            return False

        parent = self._dialog_parent()

        if vlc is None:
            messagebox.showerror(
                "Falta VLC / python-vlc",
                "No se pudo cargar VLC desde Python.\n\n"
                "1) Instalá el módulo: py -m pip install python-vlc\n"
                "2) Instalá VLC de escritorio (64 bits si tu Python es de 64 bits).\n\n"
                f"Detalle: {VLC_ERROR}",
                parent=parent,
            )
            return False

        sources = self._get_sources()
        if not sources:
            messagebox.showwarning(
                "Falta la lista",
                "Pegá el enlace M3U o seleccioná un archivo (con + podés cargar varias).",
                parent=parent,
            )
            return False

        seconds = self._read_int(self.seconds_var, 1, 120)
        if seconds is None:
            messagebox.showerror(
                "Tiempo incorrecto", "Ingresá un tiempo entre 1 y 120 segundos.", parent=parent
            )
            return False

        mode = self.mode_var.get()
        if mode == "visual":
            workers = 1
        else:
            workers = self._read_int(self.workers_var, 1, MAX_WORKERS)
            if workers is None:
                messagebox.showerror(
                    "Cantidad incorrecta",
                    f"Ingresá una cantidad de canales simultáneos entre 1 y {MAX_WORKERS}.",
                    parent=parent,
                )
                return False

        wid = None
        if mode == "visual":
            self.root.update_idletasks()
            wid = self.preview.winfo_id()

        # Reiniciar estado
        self.running = True
        self.stop_event.clear()
        self.channels = []
        self.header = "#EXTM3U"
        self.good = {}
        self.errors = []
        self.active = {}
        self.total = 0
        self.checked = 0
        self.dur_sum = 0.0
        self.workers_used = workers
        self.test_start = None
        self.test_end = None

        self.progress["value"] = 0
        self.progress_var.set("0%")
        self.count_var.set("Comprobados: 0 / 0     Funcionan: 0     Fallidos: 0")
        self.elapsed_var.set("Tiempo transcurrido: 00:00:00")
        self.remaining_var.set("Tiempo restante: calculando…")
        self.current_var.set(
            "Descargando y leyendo la lista…" if len(sources) == 1
            else f"Descargando y leyendo {len(sources)} listas…"
        )

        self.start_btn.configure(state="disabled")
        self.save_btn.configure(state="disabled")
        self.stop_btn.configure(state="normal")
        self._set_controls(False)

        self._log("-" * 60)
        self._log(f"Iniciando comprobación en modo {mode.upper()} ({len(sources)} lista(s))")

        self.worker = threading.Thread(
            target=self._run_checks,
            args=(sources, seconds, mode, workers, self.dedupe_var.get(),
                  self.audio_var.get(), wid),
            daemon=True,
        )
        self.worker.start()
        return True

    def stop(self):
        self.stop_event.set()
        self.current_var.set("Deteniendo… esperando a que terminen los canales en curso")
        self.stop_btn.configure(state="disabled")

    def on_close(self):
        self.stop_event.set()
        self.root.destroy()

    # ------------------------------------------- Hilo coordinador y workers
    @staticmethod
    def _load_lists(sources):
        """Descarga y parsea todas las listas (en paralelo, conservando el orden)."""

        def load(item):
            number, source = item
            try:
                header, channels = parse_m3u(download_m3u(source))
                return number, source, header, channels, None
            except Exception as exc:
                return number, source, None, [], str(exc)

        with ThreadPoolExecutor(max_workers=min(8, len(sources))) as pool:
            return list(pool.map(load, enumerate(sources, start=1)))

    def _run_checks(self, sources, seconds, mode, workers, dedupe, accept_audio, wid):
        instance = None
        try:
            # ---- 1) Leer y combinar todas las listas
            header = "#EXTM3U"
            channels = []
            ok_lists = 0
            errors = []

            for number, source, list_header, list_channels, error in self._load_lists(sources):
                label = f"Lista {number} ({short(source)})"
                if error:
                    errors.append(f"{label}: {error}")
                    self.events.put(("log", f"[ERROR] {label}: {error}"))
                    continue
                if not list_channels:
                    self.events.put(("log", f"[AVISO] {label}: sin canales con URL"))
                    continue

                ok_lists += 1
                self.events.put(("log", f"{label}: {len(list_channels)} canales"))
                if header.upper() == "#EXTM3U" and list_header.upper() != "#EXTM3U":
                    header = list_header  # primer encabezado con atributos (url-tvg, etc.)
                channels.extend(list_channels)

            if not channels:
                detail = "\n".join(errors)
                raise RuntimeError(
                    "No se encontraron canales con URL en las listas cargadas."
                    + (f"\n\n{detail}" if detail else "")
                )

            removed = 0
            if dedupe:
                channels, removed = dedupe_channels(channels)

            if self.stop_event.is_set():
                self.events.put(("done", True))
                return

            workers = max(1, min(workers, len(channels)))

            # ---- 2) Preparar VLC
            args = ["--intf=dummy", "--no-video-title-show", "--quiet",
                    "--no-osd", "--network-caching=1500"]
            if mode == "silencio":
                # Audio descartado: sin parlantes. Si se aceptan radios, hay que
                # decodificar el audio igual, pero enviado a una salida "dummy".
                args.append("--aout=dummy" if accept_audio else "--no-audio")
            instance = vlc.Instance(*args)
            if instance is None:
                raise RuntimeError("No se pudo iniciar VLC. Revisá que esté instalado "
                                   "y que coincida la arquitectura (32/64 bits) con Python.")

            tasks = queue.Queue()
            for index, channel in enumerate(channels, start=1):
                tasks.put((index, channel))

            # Se publican antes del evento "init" (la cola garantiza el orden).
            self.channels = channels
            self.header = header
            self.events.put(("init", len(channels), removed, workers, ok_lists, len(sources)))

            # ---- 3) Verificar
            threads = [
                threading.Thread(
                    target=self._worker_loop,
                    args=(n, instance, tasks, seconds, mode, accept_audio, wid),
                    daemon=True,
                )
                for n in range(1, workers + 1)
            ]
            for t in threads:
                t.start()
            for t in threads:
                t.join()

            self.events.put(("done", self.stop_event.is_set()))

        except Exception as exc:
            self.events.put(("fatal", str(exc)))

        finally:
            if instance is not None:
                try:
                    instance.release()
                except Exception:
                    pass

    def _worker_loop(self, number, instance, tasks, seconds, mode, accept_audio, wid):
        player = None
        sink = None  # debe vivir más que el reproductor (sus callbacks)
        try:
            player = instance.media_player_new()
            if mode == "silencio":
                sink = FrameSink()
                sink.attach(player)
            elif wid:
                embed_player(player, wid)

            while not self.stop_event.is_set():
                try:
                    index, channel = tasks.get_nowait()
                except queue.Empty:
                    break

                self.events.put(("start", index, channel.name))
                t0 = time.monotonic()
                ok, detail, resolution = self._test_channel(
                    instance, player, sink, channel.url, seconds, mode, accept_audio
                )
                if ok is None:  # interrumpido por el usuario: no cuenta
                    break
                self.events.put(
                    ("result", index, ok, detail, time.monotonic() - t0, resolution)
                )

        except Exception as exc:
            self.events.put(("log", f"[ERROR] Hilo {number}: {exc}"))

        finally:
            try:
                if player is not None:
                    player.stop()
                    player.release()
            except Exception:
                pass

    # ------------------------------------------------------ Prueba de canal
    @staticmethod
    def _is_dead(state, seen_active):
        # Stopped/Ended solo valen después de haber visto actividad: justo tras
        # play() el reproductor puede seguir reportando "Stopped" un instante.
        return state == vlc.State.Error or (
            seen_active and state in (vlc.State.Ended, vlc.State.Stopped)
        )

    def _hold(self, player, seconds):
        """Espera 'seconds' vigilando el estado. Devuelve 'ok', 'dead' o 'stop'."""
        end = time.monotonic() + seconds
        while time.monotonic() < end:
            if self.stop_event.wait(0.1):
                return "stop"
            if self._is_dead(player.get_state(), True):
                return "dead"
        return "ok"

    def _test_channel(self, instance, player, sink, url, seconds, mode, accept_audio):
        """Devuelve (ok, detalle, resolución). ok=None si el usuario detuvo la prueba."""
        media = None
        try:
            if sink is not None:
                sink.reset()

            media = instance.media_new(url)
            media.add_option(":http-reconnect")
            player.set_media(media)
            player.play()

            if mode == "silencio":
                return self._judge_silent(player, media, sink, seconds, accept_audio)
            return self._judge_visual(player, media, seconds, accept_audio)

        except Exception as exc:
            return False, str(exc), ""

        finally:
            try:
                player.stop()
            except Exception:
                pass
            if media is not None:
                try:
                    media.release()
                except Exception:
                    pass

    def _judge_silent(self, player, media, sink, seconds, accept_audio):
        active_states = (vlc.State.Opening, vlc.State.Buffering, vlc.State.Playing)
        deadline = time.monotonic() + STARTUP_TIMEOUT
        seen_active = False
        playing_since = None
        audio_only = False
        state = None

        # 1) Esperar el primer cuadro (o detectar fallo / solo audio)
        while time.monotonic() < deadline:
            if self.stop_event.wait(0.1):
                return None, "Detenido", ""
            if sink.frames > 0:
                break

            state = player.get_state()
            if state in active_states:
                seen_active = True
            if self._is_dead(state, seen_active):
                break

            if state == vlc.State.Playing:
                now = time.monotonic()
                if playing_since is None:
                    playing_since = now
                elif (accept_audio and now - playing_since >= AUDIO_GRACE
                      and player.video_get_track_count() <= 0
                      and player.audio_get_track_count() > 0):
                    audio_only = True
                    break

        if audio_only:
            result = self._hold(player, seconds)
            if result == "stop":
                return None, "Detenido", ""
            if result == "ok" and player.get_state() == vlc.State.Playing:
                return True, f"Solo audio: reproducción estable durante {seconds} s", ""
            return False, "El audio se interrumpió antes de completar la prueba", ""

        if sink.frames == 0:
            if state == vlc.State.Error:
                return False, "VLC reportó un error al abrir el stream", ""
            if self._is_dead(state, seen_active):
                return False, "El stream terminó sin entregar video", ""
            return False, f"No se recibieron cuadros de video en {STARTUP_TIMEOUT} s", ""

        # 2) Ventana de verificación: los cuadros deben seguir llegando
        forced_size = (sink.width, sink.height)
        width, height = get_video_resolution(player, media, forced_size)
        first = sink.frames

        if self._hold(player, seconds) == "stop":
            return None, "Detenido", ""

        # Se vuelve a leer al final: suele ser más fiable (sobre todo en streams HLS).
        w2, h2 = get_video_resolution(player, media, forced_size)
        if w2 > 0 and h2 > 0:
            width, height = w2, h2
        label = classify_resolution(width, height)

        gained = sink.frames - first
        needed = max(2, int(seconds * MIN_FPS))
        if gained >= needed:
            res_text = f"{width}x{height} ({label}) · " if label else "resolución no detectada · "
            return True, f"{res_text}{sink.frames} cuadros (+{gained} en {seconds} s)", label
        return False, (f"Video inestable: solo {gained} cuadros nuevos en {seconds} s "
                       f"(mínimo {needed})"), ""

    def _judge_visual(self, player, media, seconds, accept_audio):
        deadline = time.monotonic() + STARTUP_TIMEOUT
        seen_active = False
        started = False

        while time.monotonic() < deadline:
            if self.stop_event.wait(0.1):
                return None, "Detenido", ""
            state = player.get_state()
            if state in (vlc.State.Opening, vlc.State.Buffering, vlc.State.Playing):
                seen_active = True
            if state == vlc.State.Playing:
                started = True
                break
            if self._is_dead(state, seen_active):
                break

        if not started:
            return False, f"VLC no pudo iniciar la reproducción en {STARTUP_TIMEOUT} s", ""

        result = self._hold(player, seconds)
        if result == "stop":
            return None, "Detenido", ""

        state = player.get_state()
        if result != "ok" or state != vlc.State.Playing:
            return False, f"La reproducción se interrumpió (estado VLC: {state})", ""

        if player.video_get_track_count() > 0:
            width, height = get_video_resolution(player, media)
            label = classify_resolution(width, height)
            res_text = f"{width}x{height} ({label}) · " if label else "resolución no detectada · "
            return True, f"{res_text}reproducción con video estable durante {seconds} s", label
        if accept_audio:
            return True, f"Solo audio: reproducción estable durante {seconds} s", ""
        return False, "Reproduce, pero sin pista de video", ""

    # ------------------------------------------------------ Eventos hacia UI
    def _process_events(self):
        try:
            while True:
                event = self.events.get_nowait()
                kind = event[0]

                if kind == "init":
                    _, total, removed, workers, ok_lists, n_sources = event
                    self.total = total
                    self.workers_used = workers
                    self.test_start = time.monotonic()
                    msg = f"Lista combinada: {total} canales"
                    if n_sources > 1:
                        msg += f" (de {ok_lists} de {n_sources} listas)"
                    if removed:
                        msg += f", {removed} duplicados eliminados"
                    msg += f". Verificando {workers} a la vez."
                    self._log(msg)
                    self.count_var.set(
                        f"Comprobados: 0 / {total}     Funcionan: 0     Fallidos: 0"
                    )

                elif kind == "start":
                    _, index, name = event
                    self.active[index] = name
                    self._refresh_current()

                elif kind == "result":
                    self._handle_result(*event[1:])

                elif kind == "log":
                    self._log(event[1])

                elif kind == "fatal":
                    self._log("[ERROR] " + event[1].splitlines()[0])
                    messagebox.showerror("Error", event[1], parent=self._dialog_parent())
                    self._finish()

                elif kind == "done":
                    stopped = event[1]
                    if stopped:
                        text = "Comprobación detenida."
                    elif self.checked < self.total:
                        text = "Comprobación incompleta (hubo errores con VLC)."
                    else:
                        text = "Comprobación finalizada."
                    self.current_var.set(text)
                    self._log(
                        f"Finalizado. Funcionan: {len(self.good)}; fallidos: {len(self.errors)}; "
                        f"comprobados: {self.checked}/{self.total}; "
                        f"tiempo: {fmt_time(self._elapsed())}."
                    )
                    summary = self._resolution_summary()
                    if summary:
                        self._log("Resoluciones de los canales que funcionan ? " + summary)
                    self._finish()

        except queue.Empty:
            pass

        self.root.after(100, self._process_events)

    def _handle_result(self, index, ok, detail, duration, resolution):
        channel = self.channels[index - 1]
        channel.resolution = resolution
        self.active.pop(index, None)
        self.checked += 1
        self.dur_sum += duration

        if ok:
            self.good[index] = channel
        else:
            self.errors.append((channel.name, detail))

        tag = f" [{resolution}]" if resolution else ""
        self._log(f"[{'OK' if ok else 'FALLÓ'}] {channel.name}{tag} — {detail}")

        percent = self.checked / self.total * 100 if self.total else 0
        self.progress["value"] = percent
        self.progress_var.set(f"{percent:.1f}%")
        self.count_var.set(
            f"Comprobados: {self.checked} / {self.total}     "
            f"Funcionan: {len(self.good)}     Fallidos: {len(self.errors)}"
        )
        self._refresh_current()
        self._update_clock()

    def _resolution_summary(self):
        counts = {}
        for channel in self.good.values():
            key = channel.resolution or "sin detectar"
            counts[key] = counts.get(key, 0) + 1
        if not counts:
            return ""

        def order(key):
            return (RES_ORDER.index(key), key) if key in RES_ORDER else (len(RES_ORDER), key)

        return " · ".join(f"{k}: {counts[k]}" for k in sorted(counts, key=order))

    def _refresh_current(self):
        if not self.running or not self.active or self.stop_event.is_set():
            return

        if self.workers_used == 1:
            index, name = next(iter(self.active.items()))
            self.current_var.set(f"Probando canal {index} de {self.total}: {name}")
            return

        names = [n if len(n) <= 28 else n[:27] + "…" for n in self.active.values()]
        text = f"Probando {len(names)} canales a la vez: " + ", ".join(names[:3])
        if len(names) > 3:
            text += f" y {len(names) - 3} más"
        self.current_var.set(text)

    # --------------------------------------------------------------- Tiempos
    def _elapsed(self):
        if self.test_start is None:
            return 0.0
        end = self.test_end if self.test_end is not None else time.monotonic()
        return end - self.test_start

    def _estimate_remaining(self):
        """Estimación según la duración media por canal y los canales en paralelo."""
        if self.checked == 0:
            return None
        remaining = max(self.total - self.checked, 0)
        if remaining == 0:
            return 0.0
        avg = self.dur_sum / self.checked
        effective = max(1, min(self.workers_used, remaining))
        return avg * remaining / effective

    def _update_clock(self):
        if self.test_start is None:
            return
        self.elapsed_var.set(f"Tiempo transcurrido: {fmt_time(self._elapsed())}")

        if self.running:
            eta = self._estimate_remaining()
            self.remaining_var.set(
                "Tiempo restante: calculando…" if eta is None
                else f"Tiempo restante: {fmt_time(eta)}"
            )
        else:
            done_all = self.total > 0 and self.checked >= self.total
            self.remaining_var.set(
                "Tiempo restante: 00:00:00" if done_all else "Tiempo restante: --:--:--"
            )

    def _tick_clock(self):
        if self.running:
            self._update_clock()
        self.root.after(500, self._tick_clock)

    # ---------------------------------------------------------------- Cierre
    def _finish(self):
        if self.test_start is not None and self.test_end is None:
            self.test_end = time.monotonic()
        self.running = False
        self.active.clear()
        self._update_clock()

        self._set_controls(True)
        self.start_btn.configure(state="normal")
        self.stop_btn.configure(state="disabled")
        self.save_btn.configure(state="normal" if self.good else "disabled")

    def save(self):
        if not self.good:
            return

        path = filedialog.asksaveasfilename(
            title="Guardar canales funcionales",
            defaultextension=".m3u",
            initialfile=OUTPUT_NAME,
            filetypes=[("Lista M3U", "*.m3u")],
        )
        if not path:
            return

        try:
            with open(path, "w", encoding="utf-8") as f:
                f.write(self.header + "\n")
                for index in sorted(self.good):  # respeta el orden original
                    channel = self.good[index]
                    for line in with_resolution(channel.meta, channel.name, channel.resolution):
                        f.write(line + "\n")
                    f.write(channel.url + "\n")

            messagebox.showinfo(
                "Lista guardada",
                f"Se guardaron {len(self.good)} canales en:\n{path}",
            )
        except Exception as exc:
            messagebox.showerror("Error al guardar", str(exc))


def main():
    if sys.platform.startswith("win"):
        try:
            ctypes.windll.shcore.SetProcessDpiAwareness(1)  # UI nítida con escalado
        except Exception:
            pass

    root = tk.Tk()
    IPTVChecker(root)
    root.mainloop()


if __name__ == "__main__":
    main()