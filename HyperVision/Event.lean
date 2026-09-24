import HyperVision.Geometry

/-!
# Events

Keyboard, mouse and resize events delivered to views.
-/

namespace HyperVision

structure Modifiers where
  shift : Bool := false
  alt : Bool := false
  ctrl : Bool := false
deriving BEq, DecidableEq, Repr, Inhabited

namespace Modifiers
def none : Modifiers := {}
def isNone (m : Modifiers) : Bool := !m.shift && !m.alt && !m.ctrl
end Modifiers

inductive Key where
  | char (c : Char)
  | enter | escape | tab | backspace | delete | insert
  | up | down | left | right
  | home | «end» | pageUp | pageDown
  | f (n : Nat)
deriving BEq, DecidableEq, Repr, Inhabited

structure KeyEvent where
  key : Key
  mods : Modifiers := {}
deriving BEq, DecidableEq, Repr, Inhabited

namespace KeyEvent

def plain (k : Key) : KeyEvent := ⟨k, {}⟩
def alt (c : Char) : KeyEvent := ⟨.char c, { alt := true }⟩
def ctrl (c : Char) : KeyEvent := ⟨.char c, { ctrl := true }⟩

/-- The printable character typed, if this is plain (or shifted) text input. -/
def text? (k : KeyEvent) : Option Char :=
  match k.key with
  | .char c =>
    let n := c.toNat
    if !k.mods.alt && !k.mods.ctrl && n ≥ 32 && !(0x7F ≤ n && n < 0xA0) then some c else none
  | _ => none

/-- Canonical form for shortcut matching: letters typed with Alt or Ctrl ignore case and Shift. -/
def normalize (k : KeyEvent) : KeyEvent :=
  match k.key with
  | .char c => if k.mods.alt || k.mods.ctrl then ⟨.char c.toLower, { k.mods with shift := false }⟩ else k
  | _ => k

/-- Whether a key press triggers the shortcut `binding`. -/
def triggers (k binding : KeyEvent) : Bool := k.normalize == binding.normalize

/-- Human-readable name, e.g. `Alt-X` or `F10` (used in menus and the status line). -/
def label (k : KeyEvent) : String :=
  let base := match k.key with
    | .char c => (String.singleton c).toUpper
    | .enter => "Enter" | .escape => "Esc" | .tab => "Tab" | .backspace => "BkSp"
    | .delete => "Del" | .insert => "Ins" | .up => "Up" | .down => "Down"
    | .left => "Left" | .right => "Right" | .home => "Home" | .end => "End"
    | .pageUp => "PgUp" | .pageDown => "PgDn" | .f n => s!"F{n}"
  (if k.mods.ctrl then "Ctrl-" else "") ++ (if k.mods.alt then "Alt-" else "") ++
    (if k.mods.shift then "Shift-" else "") ++ base

end KeyEvent

inductive MouseButton where
  | left | middle | right | none
deriving BEq, DecidableEq, Repr, Inhabited

inductive MouseAction where
  | press | release | drag | move | wheelUp | wheelDown
deriving BEq, DecidableEq, Repr, Inhabited

structure MouseEvent where
  pos : Point
  button : MouseButton
  action : MouseAction
  mods : Modifiers := {}
  /-- `true` for the second press of a double click. -/
  double : Bool := false
deriving BEq, Repr, Inhabited

namespace MouseEvent
/-- The same event with its position made relative to `o`. -/
def relativeTo (m : MouseEvent) (o : Point) : MouseEvent := { m with pos := m.pos - o }
def isPress (m : MouseEvent) : Bool := m.action == .press && m.button == .left
end MouseEvent

inductive Event where
  | key (k : KeyEvent)
  | mouse (m : MouseEvent)
  | resize (width height : Nat)
deriving BEq, Repr, Inhabited

end HyperVision
