import HyperVision.Widget

/-!
# List boxes

Turbo Vision's `TListBox`: a single column of strings, one of which has the focus,
with a vertical scroll bar in the right-most column that tracks the focused item.

Moving the focus is reported with `Reply.changed`; `Space` and a double click report
`Reply.activated`, which presses the window's default button (so does `Enter`, which
the list leaves to the window). Printable keys are not text for a list box, so plain
letters remain hot keys of the dialog around it.
-/

namespace HyperVision

structure ListBox where
  items : Array String := #[]
  focused : Nat := 0
  /-- The item in the top row. -/
  top : Nat := 0
  /-- While the button is held after a press on the scroll bar: whether it grabbed the thumb. -/
  scrollGrab : Option Bool := none
deriving Inhabited, Repr

namespace ListBox

/-- Rows of items. -/
def rows (s : Size) : Nat := max s.h 1

/-- Columns of text: all but the right-most one, which holds the scroll bar. -/
def textWidth (s : Size) : Nat := s.w - 1

/-- Focuses item `i` (clamped to the list), scrolling as little as possible so that it
is visible (`TListViewer::focusItem`). -/
def focusItem (l : ListBox) (s : Size) (i : Int) : ListBox :=
  let f := (clampInt i 0 (l.items.size - 1 : Nat)).toNat
  let top :=
    if f < l.top then f
    else if f ≥ l.top + rows s then f + 1 - rows s
    else l.top
  { l with focused := f, top }

/-- Scrolls so that the focused item is shown at size `s` (after a resize or a new list). -/
def adjust (l : ListBox) (s : Size) : ListBox := l.focusItem s l.focused

/-- Replaces the items, keeping the focus on the same position as far as possible. -/
def setItems (l : ListBox) (items : Array String) : ListBox :=
  { l with items, focused := min l.focused (items.size - 1), scrollGrab := none }

/-- The focused item's index, unless the list is empty. -/
def focused? (l : ListBox) : Option Nat := if l.focused < l.items.size then some l.focused else none

def handleKey (l : ListBox) (s : Size) (k : KeyEvent) : ListBox × Reply :=
  let l := l.adjust s
  let f : Int := l.focused
  let go (i : Int) : ListBox × Reply := (l.focusItem s i, .changed)
  if k.mods.alt then (l, .ignored) else
  match k.key with
  | .up => go (f - 1)
  | .down => go (f + 1)
  | .pageUp => go (f - rows s)
  | .pageDown => go (f + rows s)
  | .home => go 0
  | .end => go (l.items.size - 1 : Nat)
  | .char ' ' => if k.mods.isNone && l.focused < l.items.size then (l, .activated) else (l, .ignored)
  | _ => (l, .ignored)

/-- The scroll bar in the right-most column; its value is the focused item. -/
def scrollBar (l : ListBox) (s : Size) : ScrollBar :=
  { vertical := true, length := s.h, value := l.focused, max := l.items.size - 1 }

def handleMouse (l : ListBox) (s : Size) (m : MouseEvent) : ListBox × Reply :=
  let l := l.adjust s
  let f : Int := l.focused
  let p := m.pos
  let onBar := p.x == ((textWidth s : Nat) : Int) && 0 ≤ p.y && p.y < s.h
  let inList := 0 ≤ p.x && p.x < textWidth s && 0 ≤ p.y && p.y < rows s
  match m.action with
  | .wheelUp => (l.focusItem s (f - 1), .changed)
  | .wheelDown => (l.focusItem s (f + 1), .changed)
  | .press =>
    if onBar then
      -- The scroll bar: arrows step an item, the page areas a page, the thumb is grabbed.
      let sb := l.scrollBar s
      match sb.hit p.y.toNat with
      | .thumb => ({ l with scrollGrab := some true }, .handled)
      | part =>
        let delta : Int := match part with
          | .decArrow => -1 | .incArrow => 1 | .pageDec => -(rows s : Int) | _ => rows s
        ({ l.focusItem s (f + delta) with scrollGrab := some false }, .changed)
    else if inList then
      let i := l.top + p.y
      if m.double && i < l.items.size then (l.focusItem s i, .activated) else (l.focusItem s i, .changed)
    else (l, .handled)
  | .drag =>
    match l.scrollGrab with
    | some true => (l.focusItem s ((l.scrollBar s).valueAt p.y.toNat), .changed)
    | some false => (l, .handled)
    | none =>
      -- Dragging above or below the list scrolls it an item at a time (`TListViewer`).
      if p.y < 0 then (l.focusItem s (f - 1), .changed)
      else if p.y ≥ rows s then (l.focusItem s (f + 1), .changed)
      else (l.focusItem s (l.top + p.y), .changed)
  | .release => ({ l with scrollGrab := none }, .handled)
  | .move => (l, .ignored)

def draw (l : ListBox) (ctx : DrawCtx) : DrawM Unit := do
  let c := ctx.theme.dialog
  let s := ctx.size
  let l := l.adjust s
  let w := textWidth s
  for y in [0:rows s] do
    let item := l.top + y
    let attr :=
      if item == l.focused && item < l.items.size then
        if ctx.focused then c.listFocused else c.listSelected
      else c.listNormal
    Draw.hline 0 y w ' ' attr
    match l.items[item]? with
    | some text => Draw.putStr 1 y (String.ofList (text.toList.take (w - 2))) attr
    | none => if item == 0 then Draw.putStr 1 y "<empty>" c.listNormal
  (l.scrollBar s).draw w 0 c.scrollPage c.scrollControls

end ListBox

instance : Widget ListBox where
  draw := ListBox.draw
  handleKey := ListBox.handleKey
  handleMouse := ListBox.handleMouse
  cancelMouse l := { l with scrollGrab := none }

end HyperVision
