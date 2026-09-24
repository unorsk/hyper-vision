import HyperVision.Screen
import HyperVision.Text
import HyperVision.Event
import HyperVision.Theme

/-!
# Widgets

The `Widget` class is the uniform interface of all controls: pure drawing into a
`DrawM` region plus pure event handlers that return the updated widget and a
`Reply` telling the owning window what happened.
-/

namespace HyperVision

structure Size where
  w : Nat
  h : Nat
deriving BEq, DecidableEq, Repr, Inhabited

/--
Commands flow from buttons, menus and the status line to the application.
`α` is the application's own command type.
-/
inductive Command (α : Type) where
  | quit
  | close
  | zoom
  /-- Move and resize the active window with the keyboard. -/
  | resize
  | nextWindow
  | prevWindow
  | tile
  | cascade
  | menu
  /-- Accept and close the dialog the command came from. -/
  | ok
  /-- Dismiss the dialog the command came from. -/
  | cancel
  | user (a : α)
deriving BEq, Repr, Inhabited

/-- Everything a control needs to draw itself. -/
structure DrawCtx where
  theme : Theme
  size : Size
  /-- The control owns the keyboard focus in the active window. -/
  focused : Bool
  /-- Labels: the linked control is focused. Buttons: acts as the default button. -/
  emphasized : Bool := false
  /-- The control lives in a dialog (rather than a plain window). -/
  inDialog : Bool := true
  /-- Colors of the owning window class. -/
  window : WindowColors

/-- What a widget reports after handling an event. -/
inductive Reply where
  /-- Not interested; the owner may handle the event. -/
  | ignored
  | handled
  /-- The widget was "pressed" (buttons). -/
  | activated
  /-- Move the focus to the control with this name (labels). -/
  | focus (name : String)
  /-- Open a drop-down list under `anchor` (widget-local) highlighting `current`. -/
  | dropDown (anchor : Rect) (items : Array String) (current : Nat)
deriving BEq, Repr, Inhabited

class Widget (W : Type) where
  draw : W → DrawCtx → DrawM Unit
  handleKey : W → Size → KeyEvent → W × Reply := fun w _ _ => (w, .ignored)
  /-- Mouse events in widget-local coordinates. After a press the widget receives
  every drag and the release, even outside its bounds. -/
  handleMouse : W → Size → MouseEvent → W × Reply := fun w _ _ => (w, .ignored)
  focusable : W → Bool := fun _ => true
  /-- Reacts to a hot key (`Alt+c`, or plain `c` when the focus does not take text). -/
  hotkey : W → Char → Option (W × Reply) := fun _ _ => none
  /-- Hardware cursor position while focused. -/
  cursor? : W → Size → Option Point := fun _ _ => none
  /-- Printable keys are text for this widget, so plain letters are not hot keys. -/
  wantsText : W → Bool := fun _ => false
  /-- Called when the widget gains the focus. -/
  onFocus : W → W := id
  /-- Abandons a mouse interaction whose release was lost. -/
  cancelMouse : W → W := id

/-! ## Scroll bars -/

/-- A scroll bar's state: `value` ranges over `0‥max`. -/
structure ScrollBar where
  vertical : Bool
  /-- Length in cells, including both arrows. -/
  length : Nat
  value : Nat
  max : Nat
deriving Repr, Inhabited

/-- The part of a scroll bar under the mouse. -/
inductive ScrollPart where
  | decArrow | incArrow | pageDec | pageInc | thumb
deriving BEq, Repr, Inhabited

namespace ScrollBar

/-- Offset of the thumb along the bar (as in Turbo Vision's `TScrollBar::getPos`). -/
def thumb (sb : ScrollBar) : Nat :=
  if sb.max == 0 || sb.length < 3 then 1
  else (min sb.value sb.max * (sb.length - 3) + sb.max / 2) / sb.max + 1

def hit (sb : ScrollBar) (offset : Nat) : ScrollPart :=
  if offset == 0 then .decArrow
  else if offset + 1 ≥ sb.length then .incArrow
  else if offset < sb.thumb then .pageDec
  else if offset > sb.thumb then .pageInc
  else .thumb

/-- The value corresponding to a thumb dragged to `offset`. -/
def valueAt (sb : ScrollBar) (offset : Nat) : Nat :=
  if sb.length ≤ 3 then 0
  else min sb.max (((offset - 1) * sb.max + (sb.length - 3) / 2) / (sb.length - 3))

def draw (sb : ScrollBar) (x y : Int) (page controls : Attr) : DrawM Unit := do
  let at_ (i : Nat) (ch : Char) (attr : Attr) : DrawM Unit :=
    if sb.vertical then Draw.putChar x (y + i) ch attr else Draw.putChar (x + i) y ch attr
  for i in [1:sb.length - 1] do at_ i '▒' page
  at_ 0 (if sb.vertical then '▲' else '◄') controls
  at_ (sb.length - 1) (if sb.vertical then '▼' else '►') controls
  if sb.length ≥ 3 then at_ sb.thumb '■' controls

end ScrollBar

end HyperVision
