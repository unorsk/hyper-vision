import HyperVision
import Plausible

/-!
# Test oracles and generators

Independent reference implementations used by the property tests:

* an xterm encoder for key presses and SGR mouse reports (the inverse the decoder
  must agree with);
* an ANSI interpreter that plays the renderer's output on a model terminal;
* random generators for events, screens and windows.
-/

namespace HyperVisionTests

open HyperVision Plausible

/-! ## Generators -/

/-- A number in `[lo, hi]`. -/
def natIn (lo hi : Nat) : Gen Nat := do
  let ⟨v, _⟩ ← Gen.choose Nat lo (max lo hi) (by omega)
  pure v

def pick {α : Type} [Inhabited α] (xs : Array α) : Gen α := do
  pure (xs[(← natIn 0 (xs.size - 1))]?.getD default)

def genBool : Gen Bool := do pure ((← natIn 0 1) == 1)

/-! ## xterm input encoding (independent of the decoder) -/

def bytes (s : String) : List UInt8 := s.toUTF8.toList

def modParam (m : Modifiers) : Nat :=
  1 + (if m.shift then 1 else 0) + (if m.alt then 2 else 0) + (if m.ctrl then 4 else 0)

/-- How xterm sends a key press, when that key press can be sent unambiguously. -/
def encodeKey (k : KeyEvent) : Option (List UInt8) :=
  let letter (f : Char) : List UInt8 :=
    if k.mods.isNone then bytes s!"\x1b[{f}" else bytes s!"\x1b[1;{modParam k.mods}{f}"
  let tilde (n : Nat) : List UInt8 :=
    if k.mods.isNone then bytes s!"\x1b[{n}~" else bytes s!"\x1b[{n};{modParam k.mods}~"
  match k.key with
  | .up => letter 'A' | .down => letter 'B' | .right => letter 'C' | .left => letter 'D'
  | .home => letter 'H' | .end => letter 'F'
  | .insert => tilde 2 | .delete => tilde 3 | .pageUp => tilde 5 | .pageDown => tilde 6
  | .f n =>
    if 1 ≤ n && n ≤ 4 then
      let f := "PQRS".toList[n - 1]!
      some (if k.mods.isNone then bytes s!"\x1bO{f}" else letter f)
    else match n with
      | 5 => tilde 15 | 6 => tilde 17 | 7 => tilde 18 | 8 => tilde 19 | 9 => tilde 20
      | 10 => tilde 21 | 11 => tilde 23 | 12 => tilde 24 | _ => none
  | .enter => if k.mods.isNone then some [13] else none
  | .tab =>
    if k.mods.isNone then some [9] else if k.mods == { shift := true } then bytes "\x1b[Z" else none
  | .backspace => if k.mods.isNone then some [127] else none
  | .escape => none
  | .char c =>
    let n := c.toNat
    let printable := n ≥ 32 && n != 127
    if k.mods.isNone && printable then some (bytes (String.singleton c))
    else if k.mods == { ctrl := true } && 'a' ≤ c && c ≤ 'z' && !"hijm".toList.contains c then
      some [(n - 96).toUInt8]
    else if k.mods == { alt := true } && printable && n < 127 && c != '[' && c != 'O' then
      some (0x1b :: bytes (String.singleton c))
    else none

/-- How xterm reports a mouse event in SGR mode. -/
def encodeMouse (m : MouseEvent) : Option (List UInt8) :=
  if m.pos.x < 0 || m.pos.y < 0 || m.double then none else
  let btn : Nat := match m.button with | .left => 0 | .middle => 1 | .right => 2 | .none => 3
  let mods := (if m.mods.shift then 4 else 0) + (if m.mods.alt then 8 else 0) +
    (if m.mods.ctrl then 16 else 0)
  let code? : Option Nat := match m.action, m.button with
    | .press, .none => none
    | .press, _ => some btn
    | .release, .none => none
    | .release, _ => some btn
    | .drag, .none => none
    | .drag, _ => some (btn + 32)
    | .move, .none => some (3 + 32)
    | .move, _ => none
    | .wheelUp, .left => some 64
    | .wheelDown, .middle => some 65
    | _, _ => none
  code?.map fun code =>
    bytes s!"\x1b[<{code + mods};{m.pos.x + 1};{m.pos.y + 1}{if m.action == .release then 'm' else 'M'}"

def encodeEvent : Event → Option (List UInt8)
  | .key k => encodeKey k
  | .mouse m => encodeMouse m
  | .resize .. => none

def genMods : Gen Modifiers := do
  pure { shift := ← genBool, alt := ← genBool, ctrl := ← genBool }

def genChar : Gen Char := do
  match ← natIn 0 3 with
  | 0 => pure (Char.ofNat (← natIn 32 126))
  | 1 => pure (Char.ofNat (← natIn 0xA0 0x7FF))
  | 2 => pure (Char.ofNat (← natIn 0x800 0xD7FF))
  | _ => pure (Char.ofNat (← natIn 0x10000 0x10FFFF))

def genKey : Gen Key := do
  match ← natIn 0 13 with
  | 0 => pure .up | 1 => pure .down | 2 => pure .left | 3 => pure .right
  | 4 => pure .home | 5 => pure .end | 6 => pure .insert | 7 => pure .delete
  | 8 => pure .pageUp | 9 => pure .pageDown | 10 => pure (.f (← natIn 1 12))
  | 11 => pick #[.enter, .tab, .backspace]
  | _ => pure (.char (← genChar))

/-- A random key press that has an xterm encoding. -/
def genKeyEvent : Gen KeyEvent := do
  for _ in [0:50] do
    let k : KeyEvent := ⟨← genKey, ← genMods⟩
    if (encodeKey k).isSome then return k
  pure ⟨.char 'a', {}⟩

def genMouseEvent : Gen MouseEvent := do
  let pos : Point := ⟨← natIn 0 300, ← natIn 0 300⟩
  let mods ← genMods
  match ← natIn 0 5 with
  | 0 => pure { pos, mods, button := ← pick #[.left, .middle, .right], action := .press }
  | 1 => pure { pos, mods, button := ← pick #[.left, .middle, .right], action := .release }
  | 2 => pure { pos, mods, button := ← pick #[.left, .middle, .right], action := .drag }
  | 3 => pure { pos, mods, button := .none, action := .move }
  | 4 => pure { pos, mods, button := .left, action := .wheelUp }
  | _ => pure { pos, mods, button := .middle, action := .wheelDown }

def genEvent : Gen Event := do
  if ← genBool then pure (.key (← genKeyEvent)) else pure (.mouse (← genMouseEvent))

/-! ## Arbitrary instances (no shrinking needed for these structured values) -/

instance : Arbitrary KeyEvent := ⟨genKeyEvent⟩
instance : Shrinkable KeyEvent := {}
instance : Arbitrary MouseEvent := ⟨genMouseEvent⟩
instance : Shrinkable MouseEvent := {}
instance : Arbitrary Event := ⟨genEvent⟩
instance : Shrinkable Event := {}

/-! ## Screens -/

def genColor : Gen Color := do pure (Color.ofIndex ⟨(← natIn 0 15) % 16, Nat.mod_lt _ (by decide)⟩)

/-- Characters the renderer must reproduce, including box drawing, blocks and controls. -/
def charPool : Array Char :=
  #[' ', 'a', 'Z', '0', '~', '─', '│', '┌', '╔', '═', '░', '▒', '▄', '▀', '■', '↑', '►', 'é', 'Ω',
    Char.ofNat 7, Char.ofNat 27, Char.ofNat 0x85]

def genCell : Gen Cell := do pure { ch := ← pick charPool, attr := ⟨← genColor, ← genColor⟩ }

def genScreen (w h : Nat) : Gen Screen := do
  let mut s := Screen.new w h
  for y in [0:h] do
    for x in [0:w] do
      s := s.set x y (← genCell)
  pure s

/-- A pair of equally sized screens where the second is the first with random changes. -/
structure ScreenPair where
  prev : Screen
  next : Screen

def genScreenPair : Gen ScreenPair := do
  let w ← natIn 1 12
  let h ← natIn 1 6
  let prev ← genScreen w h
  let mut next := prev
  for y in [0:h] do
    for x in [0:w] do
      if (← natIn 0 2) == 0 then next := next.set x y (← genCell)
  pure ⟨prev, next⟩

def showScreen (s : Screen) : String :=
  "\n".intercalate <| (List.range s.height).map fun (y : Nat) =>
    String.ofList <| (List.range s.width).map fun (x : Nat) => ((s.get? x y).map (·.ch)).getD '?'

instance : Repr ScreenPair := ⟨fun p _ => s!"prev:\n{showScreen p.prev}\nnext:\n{showScreen p.next}"⟩
instance : Arbitrary ScreenPair := ⟨genScreenPair⟩
instance : Shrinkable ScreenPair := {}

/-! ## A model terminal that interprets ANSI output (independent of `Terminal.Op`) -/

structure TermModel where
  grid : Screen
  x : Int
  y : Int
  attr : Attr

def colorOfRGB (r g b : Nat) : Color :=
  (List.range 16).foldl (init := .black) fun acc i =>
    let c := Color.ofIndex ⟨i % 16, Nat.mod_lt _ (by decide)⟩
    let (cr, cg, cb) := c.rgb
    if cr.toNat == r && cg.toNat == g && cb.toNat == b then c else acc

def applySgr (a : Attr) (params : List Nat) : Attr :=
  match params with
  | [0] => ⟨.lightGray, .black⟩
  | [38, 2, r, g, b, 48, 2, r', g', b'] => ⟨colorOfRGB r g b, colorOfRGB r' g' b'⟩
  | _ => a

/-- Plays terminal output on the model terminal. -/
def interpret (t : TermModel) (out : String) : TermModel := Id.run do
  let mut t := t
  let mut cs := out.toList
  for _ in [0:out.length] do
    match cs with
    | [] => break
    | '\x1b' :: '[' :: rest =>
      let paramChars := rest.takeWhile fun c => !('@' ≤ c && c ≤ '~')
      match rest.drop paramChars.length with
      | final :: rest' =>
        cs := rest'
        let ps := String.ofList paramChars
        if ps.startsWith "?" then continue
        let nums : List Nat := (ps.splitOn ";").map fun p => p.toNat?.getD 0
        match final with
        | 'H' => t := { t with y := ((nums[0]?.getD 1 : Nat) : Int) - 1, x := ((nums[1]?.getD 1 : Nat) : Int) - 1 }
        | 'm' => t := { t with attr := applySgr t.attr nums }
        | 'J' => t := { t with grid := Screen.new t.grid.width t.grid.height }
        | _ => pure ()
      | [] => cs := []
    | c :: rest =>
      t := { t with grid := t.grid.set t.x t.y ⟨c, t.attr⟩, x := t.x + 1 }
      cs := rest
  return t

/-! ## Windows -/

def genWindow : Gen (Window Unit) := do
  let w ← natIn 10 60
  let h ← natIn 3 20
  let flags : WindowFlags := { move := ← genBool, grow := ← genBool, close := ← genBool, zoom := ← genBool }
  let style ← pick #[WindowStyle.blue, .cyan, .gray, .dialog]
  pure { title := "T", bounds := ⟨0, 0, w, h⟩, flags, style }

instance : Repr (Window Unit) := ⟨fun w _ => s!"window {w.bounds.w}x{w.bounds.h} flags {repr w.flags}"⟩
instance : Arbitrary (Window Unit) := ⟨genWindow⟩
instance : Shrinkable (Window Unit) := {}

end HyperVisionTests
