#!/usr/bin/env python3
"""Scripted keyboard and mouse input for the hyper-vision demo.

The demo runs in its own 100x30 pseudo-terminal and its output is relayed to
stdout, so any terminal recorder can capture the session; `docs/demo.tape` records
it with VHS (see `scripts/record.sh`).
"""
import fcntl
import os
import pty
import struct
import sys
import termios
import threading
import time

BIN = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".lake", "build", "bin",
                   "hyper-vision-demo")

KEYS = {
    "enter": "\r", "esc": "\x1b", "tab": "\t", "backtab": "\x1b[Z", "backspace": "\x7f",
    "up": "\x1b[A", "down": "\x1b[B", "right": "\x1b[C", "left": "\x1b[D",
    "shift-up": "\x1b[1;2A", "shift-down": "\x1b[1;2B",
    "shift-right": "\x1b[1;2C", "shift-left": "\x1b[1;2D",
    "home": "\x1b[H", "end": "\x1b[F", "delete": "\x1b[3~", "space": " ",
    "f3": "\x1bOR", "f4": "\x1bOS", "f5": "\x1b[15~", "f6": "\x1b[17~", "f10": "\x1b[21~",
    "alt-f3": "\x1b[1;3R", "shift-f6": "\x1b[17;2~", "alt-x": "\x1bx",
    "ctrl-end": "\x1b[1;5F", "ctrl-home": "\x1b[1;5H",
}


class Demo:
    """A running demo process with helpers for synthetic input (0-based cell coordinates)."""

    def __init__(self, cols, rows, sink, mouse_cursor=True):
        pid, fd = pty.fork()
        if pid == 0:
            fcntl.ioctl(1, termios.TIOCSWINSZ, struct.pack("HHHH", rows, cols, 0, 0))
            env = dict(os.environ, TERM="xterm-256color", COLORTERM="truecolor")
            if mouse_cursor:
                env["HV_MOUSE_CURSOR"] = "1"
            os.execve(BIN, [BIN], env)
        self.pid, self.fd, self.sink = pid, fd, sink
        self.pos = (cols // 2, rows // 2)
        threading.Thread(target=self._pump, daemon=True).start()

    def _pump(self):
        while True:
            try:
                data = os.read(self.fd, 65536)
            except OSError:
                break
            if not data:
                break
            self.sink(data)

    def send(self, s):
        os.write(self.fd, s.encode() if isinstance(s, str) else s)

    def wait(self, seconds):
        time.sleep(seconds)

    def key(self, name, pause=0.35):
        self.send(KEYS.get(name, name))
        time.sleep(pause)

    def type(self, text, cps=14, pause=0.3):
        for ch in text:
            self.send(ch)
            time.sleep(1 / cps)
        time.sleep(pause)

    def _mouse(self, code, x, y, final="M"):
        self.send(f"\x1b[<{code};{x + 1};{y + 1}{final}")

    def move(self, x, y, duration=0.35, code=35):
        """Glides the mouse to (x, y), one report per cell (35: no button, 32: left held)."""
        x0, y0 = self.pos
        steps = max(abs(x - x0), abs(y - y0), 1)
        for i in range(1, steps + 1):
            p = (round(x0 + (x - x0) * i / steps), round(y0 + (y - y0) * i / steps))
            if p != self.pos:
                self._mouse(code, *p)
                self.pos = p
            time.sleep(duration / steps)

    def click(self, x, y, pause=0.35, double=False):
        self.move(x, y)
        for _ in range(2 if double else 1):
            self._mouse(0, x, y)
            time.sleep(0.07)
            self._mouse(0, x, y, "m")
            time.sleep(0.07)
        time.sleep(pause)

    def drag(self, x0, y0, x1, y1, duration=0.8, pause=0.35):
        self.move(x0, y0)
        self._mouse(0, x0, y0)
        time.sleep(0.12)
        self.move(x1, y1, duration, code=32)
        time.sleep(0.08)
        self._mouse(0, x1, y1, "m")
        time.sleep(pause)

    def quit(self):
        self.send(KEYS["alt-x"])
        os.waitpid(self.pid, 0)


def tour(d, snap=lambda name: None):
    """The scripted tour recorded for the README (100x30 terminal)."""
    d.wait(1.5)
    # Menu bar: File, then Edit (disabled items) and Window with the arrow keys.
    d.click(6, 0, pause=1.0)
    d.key("right", 1.0)
    snap("menu_edit")
    d.key("right", 1.0)
    d.key("esc", 0.2)
    d.key("esc", 0.5)
    # Dialog: input line, combo box drop-down, check boxes, radio buttons, memo.
    d.click(50, 4, double=True, pause=0.3)
    d.type("Niklaus Wirth")
    d.click(64, 6, pause=0.8)
    for _ in range(5):
        d.key("down", 0.25)
    snap("popup")
    d.key("enter", 0.6)
    d.click(33, 10, pause=0.4)
    d.click(33, 11, pause=0.4)
    d.click(56, 11, pause=0.6)
    d.click(50, 17, pause=0.3)
    d.key("ctrl-end", 0.3)
    d.key("enter", 0.1)
    d.type("Pascal, Modula-2, Oberon.")
    snap("dialog_filled")
    d.click(44, 19, pause=2.5)
    snap("values")
    d.key("enter", 0.8)
    # Windows: move by the title bar, resize from the corner.
    d.drag(24, 2, 34, 4, 0.9)
    d.drag(56, 19, 84, 26, 0.9)
    snap("moved_resized")
    # Edit > Insert > Box: a sub-menu command that edits the active window.
    d.click(40, 24, pause=0.2)
    d.key("ctrl-end", 0.1)
    d.key("enter", 0.1)
    d.key("enter", 0.3)
    d.click(12, 0, pause=0.6)
    d.click(14, 8, pause=0.8)
    snap("submenu")
    d.click(15, 12, pause=0.8)
    # A second editor, then tile and cascade from the Window menu.
    d.key("f4", 0.5)
    d.type('def hello := "world"')
    d.click(19, 0, pause=0.5)
    d.click(19, 2, pause=1.5)
    snap("tiled")
    d.click(19, 0, pause=0.5)
    d.click(19, 3, pause=1.5)
    snap("cascaded")
    # Zoom and restore with the frame icon, then switch windows with F6.
    d.click(96, 2, pause=1.0)
    d.click(96, 1, pause=1.0)
    d.key("f6", 1.0)
    # Help > About opens a modal message box.
    d.click(26, 0, pause=0.5)
    d.click(28, 2, pause=2.0)
    snap("about")
    d.click(49, 17, pause=1.5)
    snap("end")


if __name__ == "__main__":
    out = sys.stdout.buffer
    demo = Demo(100, 30, lambda b: (out.write(b), out.flush()))
    tour(demo)
    if "--hold" in sys.argv:
        # Keep the last frame on screen until the recorder stops.
        time.sleep(3600)
    demo.quit()
