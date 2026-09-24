/*
 * Minimal POSIX terminal shim for hyper-vision.
 * Raw mode, reads with a timeout, window size, and a terminal restore that also
 * runs at exit and on fatal signals.
 */
#include <lean/lean.h>
#include <errno.h>
#include <poll.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <termios.h>
#include <unistd.h>

static struct termios hv_saved;
static volatile sig_atomic_t hv_raw_active = 0;
static int hv_handlers_installed = 0;

static const char hv_reset_seq[] =
  "\x1b[?1006l\x1b[?1003l\x1b[?1002l\x1b[?1000l" /* mouse off          */
  "\x1b[0m\x1b[?7h\x1b[?25h"                    /* attrs, wrap, cursor */
  "\x1b[?1049l";                                /* main screen        */

/* Async-signal-safe: only write(2) and tcsetattr(3). */
static void hv_restore(void) {
  if (!hv_raw_active) return;
  hv_raw_active = 0;
  ssize_t unused = write(STDOUT_FILENO, hv_reset_seq, sizeof(hv_reset_seq) - 1);
  (void)unused;
  while (tcsetattr(STDIN_FILENO, TCSAFLUSH, &hv_saved) != 0 && errno == EINTR) {}
}

static void hv_on_signal(int sig) {
  hv_restore();
  signal(sig, SIG_DFL);
  raise(sig);
}

static void hv_install_handlers(void) {
  if (hv_handlers_installed) return;
  hv_handlers_installed = 1;
  atexit(hv_restore);
  /* SIGSEGV is left alone: the Lean runtime uses it to detect stack overflows. */
  const int sigs[] = { SIGTERM, SIGHUP, SIGINT, SIGQUIT, SIGABRT };
  for (size_t i = 0; i < sizeof(sigs) / sizeof(sigs[0]); i++) {
    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_handler = hv_on_signal;
    sigemptyset(&sa.sa_mask);
    sigaction(sigs[i], &sa, NULL);
  }
}

static lean_obj_res hv_error(const char *msg) {
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

static lean_obj_res hv_errno_error(void) {
  return hv_error(strerror(errno));
}

LEAN_EXPORT lean_obj_res hv_term_enable_raw(void) {
  if (hv_raw_active) return lean_io_result_mk_ok(lean_box(0));
  if (!isatty(STDIN_FILENO)) return hv_error("hyper-vision: stdin is not a terminal");
  if (tcgetattr(STDIN_FILENO, &hv_saved) != 0) return hv_errno_error();
  struct termios raw = hv_saved;
  raw.c_iflag &= ~(tcflag_t)(BRKINT | ICRNL | INPCK | ISTRIP | IXON);
  raw.c_oflag &= ~(tcflag_t)(OPOST);
  raw.c_cflag |= CS8;
  raw.c_lflag &= ~(tcflag_t)(ECHO | ICANON | IEXTEN | ISIG);
  raw.c_cc[VMIN] = 0;
  raw.c_cc[VTIME] = 0;
  hv_install_handlers();
  int rc;
  while ((rc = tcsetattr(STDIN_FILENO, TCSAFLUSH, &raw)) != 0 && errno == EINTR) {}
  if (rc != 0) return hv_errno_error();
  hv_raw_active = 1;
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res hv_term_restore(void) {
  hv_restore();
  return lean_io_result_mk_ok(lean_box(0));
}

/* Returns (cols << 16) | rows, or 80x25 when the size is unknown. */
LEAN_EXPORT lean_obj_res hv_term_size(void) {
  struct winsize ws;
  uint32_t cols = 80, rows = 25;
  if (ioctl(STDOUT_FILENO, TIOCGWINSZ, &ws) == 0 && ws.ws_col > 0 && ws.ws_row > 0) {
    cols = ws.ws_col;
    rows = ws.ws_row;
  }
  return lean_io_result_mk_ok(lean_box_uint32((cols << 16) | (rows & 0xFFFF)));
}

/*
 * Waits up to `timeout_ms` for input and returns the bytes available (possibly
 * none). Fails once the terminal is gone, so the caller cannot spin on EOF.
 */
LEAN_EXPORT lean_obj_res hv_term_read(uint32_t timeout_ms) {
  struct pollfd pfd = { .fd = STDIN_FILENO, .events = POLLIN, .revents = 0 };
  int ready = poll(&pfd, 1, (int)timeout_ms);
  if (ready < 0) {
    if (errno == EINTR) return lean_io_result_mk_ok(lean_alloc_sarray(1, 0, 0));
    return hv_errno_error();
  }
  if (ready == 0) return lean_io_result_mk_ok(lean_alloc_sarray(1, 0, 0));
  enum { CAP = 4096 };
  lean_object *buf = lean_alloc_sarray(1, 0, CAP);
  ssize_t n = read(STDIN_FILENO, lean_sarray_cptr(buf), CAP);
  if (n <= 0) {
    lean_dec(buf);
    if (n < 0 && (errno == EINTR || errno == EAGAIN))
      return lean_io_result_mk_ok(lean_alloc_sarray(1, 0, 0));
    return n == 0 ? hv_error("hyper-vision: terminal closed") : hv_errno_error();
  }
  lean_sarray_set_size(buf, (size_t)n);
  return lean_io_result_mk_ok(buf);
}

/* Writes the whole buffer to stdout, bypassing stdio buffering. */
LEAN_EXPORT lean_obj_res hv_term_write(b_lean_obj_arg bytes) {
  const uint8_t *p = lean_sarray_cptr(bytes);
  size_t left = lean_sarray_size(bytes);
  while (left > 0) {
    ssize_t n = write(STDOUT_FILENO, p, left);
    if (n < 0) {
      if (errno == EINTR || errno == EAGAIN) continue;
      return hv_errno_error();
    }
    p += n;
    left -= (size_t)n;
  }
  return lean_io_result_mk_ok(lean_box(0));
}
