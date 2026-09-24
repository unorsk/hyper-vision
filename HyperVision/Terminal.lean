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
  /-- The xterm 256-color cube: fixed colors close to CGA. -/
  | ansi256
  /-- The 16 ANSI colors: follows the terminal's own palette. -/
  | ansi16
deriving BEq, Repr, Inhabited

/--
Picks a color mode: `HV_COLORS` (`truecolor`, `256` or `16`) wins; otherwise
`COLORTERM` announces 24-bit support and a `*256color` `TERM` the 256-color palette.
-/
def detectColorMode : IO ColorMode := do
  match ← IO.getEnv "HV_COLORS" with
  | some "truecolor" | some "24bit" => return .trueColor
  | some "256" => return .ansi256
  | some "16" => return .ansi16
  | _ => pure ()
  if let some v ← IO.getEnv "COLORTERM" then
    if v == "truecolor" || v == "24bit" then return .trueColor
  let term := (← IO.getEnv "TERM").getD ""
  return if (term.splitOn "256color").length > 1 then .ansi256 else .ansi16

private def esc (s : String) : String := "\x1b[" ++ s

/-- The SGR sequence selecting an attribute. -/
def sgr (mode : ColorMode) (a : Attr) : String :=
  match mode with
  | .trueColor =>
    let (r, g, b) := a.fg.rgb
    let (br, bg, bb) := a.bg.rgb
    esc s!"38;2;{r};{g};{b};48;2;{br};{bg};{bb}m"
  | .ansi256 => esc s!"38;5;{a.fg.xterm256};48;5;{a.bg.xterm256}m"
  | .ansi16 =>
    let (f, fBright) := a.fg.ansi
    let (b, bBright) := a.bg.ansi
    esc s!"{if fBright then 90 + f else 30 + f};{if bBright then 100 + b else 40 + b}m"

/-- East Asian wide and emoji ranges: such characters take two terminal columns. -/
def isWide (c : Char) : Bool :=
  let n := c.toNat
  (0x1100 ≤ n && n ≤ 0x115F) || (0x2E80 ≤ n && n ≤ 0xA4CF) || (0xAC00 ≤ n && n ≤ 0xD7A3) ||
  (0xF900 ≤ n && n ≤ 0xFAFF) || (0xFE30 ≤ n && n ≤ 0xFE4F) || (0xFF00 ≤ n && n ≤ 0xFF60) ||
  (0xFFE0 ≤ n && n ≤ 0xFFE6) || (0x1F300 ≤ n && n ≤ 0x1FAFF) || (0x20000 ≤ n && n ≤ 0x3FFFD)

/-- Combining marks take no column of their own. -/
def isZeroWidth (c : Char) : Bool :=
  let n := c.toNat
  (0x0300 ≤ n && n ≤ 0x036F) || (0x200B ≤ n && n ≤ 0x200F) || (0xFE00 ≤ n && n ≤ 0xFE0F) ||
  (0x20D0 ≤ n && n ≤ 0x20FF)

/-- Control characters would be interpreted by the terminal; show them as blanks. -/
def printable (c : Char) : Char :=
  let n := c.toNat
  if n < 0x20 || (0x7F ≤ n && n < 0xA0) then ' ' else c

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
        let ch := printable c.ch
        out := out.push ch
        -- The terminal's idea of the cursor is unknown after a wide or zero-width
        -- character, so the next cell is positioned explicitly.
        pos := if isWide ch || isZeroWidth ch then none else some (x + 1, y)
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
