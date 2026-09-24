import HyperVision.Screen

/-!
# Terminal back end

Raw-mode control through a tiny C shim, and a differential renderer that turns a
`Screen` into ANSI escape sequences, only emitting cells that changed.
-/

namespace HyperVision.Terminal

@[extern "hv_term_enable_raw"] opaque enableRaw : IO Unit
@[extern "hv_term_restore"] opaque restore : IO Unit
@[extern "hv_term_size"] private opaque sizeRaw : IO UInt32
/-- Waits at most `timeoutMs` for input; returns the bytes available (possibly none). -/
@[extern "hv_term_read"] opaque read (timeoutMs : UInt32) : IO ByteArray
@[extern "hv_term_write"] opaque write (bytes : @& ByteArray) : IO Unit

/-- Terminal size as `(columns, rows)`. -/
def size : IO (Nat × Nat) := do
  let v ← sizeRaw
  pure ((v >>> 16).toNat, (v &&& 0xFFFF).toNat)

/-- How colors are encoded on the wire. -/
inductive ColorMode where
  /-- 24-bit RGB: exact CGA colors. -/
  | trueColor
  /-- The 16 ANSI colors: follows the terminal's own palette. -/
  | ansi16
deriving BEq, Repr, Inhabited

/-- Picks a color mode from `COLORTERM` / `HV_COLORS`. -/
def detectColorMode : IO ColorMode := do
  if (← IO.getEnv "HV_COLORS") == some "16" then return .ansi16
  match ← IO.getEnv "COLORTERM" with
  | some v => return if v == "truecolor" || v == "24bit" then .trueColor else .ansi16
  | none => return .trueColor

private def esc (s : String) : String := "\x1b[" ++ s

/-- The SGR sequence selecting an attribute. -/
def sgr (mode : ColorMode) (a : Attr) : String :=
  match mode with
  | .trueColor =>
    let (r, g, b) := a.fg.rgb
    let (br, bg, bb) := a.bg.rgb
    esc s!"38;2;{r};{g};{b};48;2;{br};{bg};{bb}m"
  | .ansi16 =>
    let (f, fBright) := a.fg.ansi
    let (b, bBright) := a.bg.ansi
    esc s!"{if fBright then 90 + f else 30 + f};{if bBright then 100 + b else 40 + b}m"

/--
Encodes the changes from `prev` to `next`. A missing or differently sized `prev`
forces a full repaint. The hardware cursor is shown at `cursor`, if given.
-/
def diff (mode : ColorMode) (prev : Option Screen) (next : Screen) (cursor : Option Point) :
    String := Id.run do
  let full := match prev with
    | some p => p.width != next.width || p.height != next.height
    | none => true
  let mut out := esc "?25l"
  if full then out := out ++ esc "0m" ++ esc "2J"
  let mut attr : Option Attr := none
  let mut pos : Option (Nat × Nat) := none
  for y in [0:next.height] do
    for x in [0:next.width] do
      let some c := next.get? x y | continue
      let same := !full && (prev.bind (·.get? x y)) == some c
      unless same do
        if pos != some (x, y) then out := out ++ esc s!"{y + 1};{x + 1}H"
        if attr != some c.attr then
          out := out ++ sgr mode c.attr
          attr := some c.attr
        out := out.push c.ch
        pos := some (x + 1, y)
  if let some p := cursor then
    out := out ++ esc s!"{p.y + 1};{p.x + 1}H" ++ esc "?25h"
  return out

/-- Alternate screen, no autowrap, hidden cursor, SGR mouse reporting. -/
def enterSequence (anyMotion : Bool) : String :=
  esc "?1049h" ++ esc "?7l" ++ esc "?25l" ++ esc "?1000h" ++ esc "?1002h" ++
    (if anyMotion then esc "?1003h" else "") ++ esc "?1006h" ++ esc "2J"

def leaveSequence : String :=
  esc "?1006l" ++ esc "?1003l" ++ esc "?1002l" ++ esc "?1000l" ++ esc "0m" ++ esc "?7h" ++
    esc "?25h" ++ esc "?1049l"

def writeString (s : String) : IO Unit := write s.toUTF8

/-- Runs `act` with the terminal in raw full-screen mode, restoring it afterwards. -/
def withTerminal {α : Type} (anyMotion : Bool) (act : IO α) : IO α := do
  enableRaw
  writeString (enterSequence anyMotion)
  try act
  finally
    writeString leaveSequence
    restore

end HyperVision.Terminal
