import HyperVision.Widget

/-!
# Buttons

Drawn exactly like `TButton::drawState`: a green face with a black half-block
shadow that disappears (and the face shifts right) while the button is held down.
-/

namespace HyperVision

structure Button (α : Type) where
  title : HotText
  command : Command α
  /-- Pressed by `Enter` when no other button has the focus. -/
  isDefault : Bool := false
  enabled : Bool := true
  /-- Visual pressed state while the mouse button is held over it. -/
  down : Bool := false
deriving Inhabited

namespace Button

variable {α : Type}

/-- The clickable face: every column but the first and last, every row but the last. -/
def faceContains (s : Size) (p : Point) : Bool :=
  1 ≤ p.x && p.x < s.w - 1 && 0 ≤ p.y && p.y < s.h - 1

def draw (b : Button α) (ctx : DrawCtx) : DrawM Unit := do
  let c := ctx.theme.dialog
  let (face, hot) :=
    if !b.enabled then (c.buttonDisabled, c.buttonDisabled)
    else if ctx.focused then (c.buttonSelected, c.buttonShortcut)
    else if ctx.emphasized then (c.buttonDefault, c.buttonShortcut)
    else (c.button, c.buttonShortcut)
  let shadow := c.buttonShadow
  let w := ctx.size.w
  let s : Nat := w - 1
  let titleRow := ctx.size.h / 2 - 1
  for y in [0:ctx.size.h - 1] do
    Draw.hline 0 y w ' ' face
    Draw.putChar 0 y ' ' shadow
    let i : Nat ← if b.down then do
        Draw.putChar 1 y ' ' shadow
        pure 2
      else do
        Draw.putChar s y (if y == 0 then '▄' else '█') shadow
        pure 1
    if y == titleRow then
      let l := max 1 ((s - b.title.width - 1) / 2)
      Draw.putHot (i + l) y b.title face hot
  let last := ctx.size.h - 1
  Draw.hline 0 last w ' ' shadow
  unless b.down do Draw.hline 2 last (s - 1) '▀' shadow

def handleMouse (b : Button α) (s : Size) (m : MouseEvent) : Button α × Reply :=
  if !b.enabled then (b, .handled) else
  match m.action with
  | .press => if faceContains s m.pos then ({ b with down := true }, .handled) else (b, .ignored)
  | .drag => ({ b with down := faceContains s m.pos }, .handled)
  | .release =>
    if b.down then ({ b with down := false }, .activated) else (b, .handled)
  | _ => (b, .ignored)

end Button

instance {α : Type} : Widget (Button α) where
  draw := Button.draw
  handleKey b _ k :=
    if b.enabled && k.mods.isNone && (k.key == .enter || k.key == .char ' ') then
      (b, .activated)
    else (b, .ignored)
  handleMouse := Button.handleMouse
  focusable b := b.enabled
  hotkey b c := if b.enabled && b.title.hotkey? == some c then some (b, .activated) else none
  cancelMouse b := { b with down := false }

end HyperVision
