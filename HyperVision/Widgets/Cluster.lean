import HyperVision.Widget

/-!
# Check boxes and radio buttons

Both are Turbo Vision "clusters": a column-major grid of items, each drawn as an
icon (` [ ] ` or ` ( ) `), a marker and a hot-key label.
-/

namespace HyperVision

namespace Cluster

/-- Left column of each column of items (column-major, `rows` items per column). -/
def columnStarts (labels : Array HotText) (rows : Nat) : Array Nat := Id.run do
  let rows := max rows 1
  let cols := (labels.size + rows - 1) / rows
  let mut xs : Array Nat := #[]
  let mut x := 0
  for c in [0:cols] do
    xs := xs.push x
    let widest := (labels.extract (c * rows) ((c + 1) * rows)).foldl (max · ·.width) 0
    x := x + widest + 6
  return xs

def itemPos (labels : Array HotText) (rows i : Nat) : Point :=
  let rows := max rows 1
  ⟨(columnStarts labels rows)[i / rows]?.getD 0, i % rows⟩

def itemAt? (labels : Array HotText) (rows : Nat) (p : Point) : Option Nat :=
  let rows := max rows 1
  let xs := columnStarts labels rows
  (List.range labels.size).find? fun i =>
    let x0 := xs[i / rows]?.getD 0
    let x1 : Int := (xs[i / rows + 1]?.map (Int.ofNat)).getD (x0 + 5 + (labels[i]?.map (·.width)).getD 0)
    p.y == ↑(i % rows) && x0 ≤ p.x && p.x < x1

def draw (labels : Array HotText) (icon : String) (marker : Nat → Char) (cursor : Nat)
    (ctx : DrawCtx) : DrawM Unit := do
  let c := ctx.theme.dialog
  Draw.fill ⟨0, 0, ctx.size.w, ctx.size.h⟩ ' ' c.cluster
  for h : i in [0:labels.size] do
    let p := itemPos labels ctx.size.h i
    let attr := if ctx.focused && i == cursor then c.clusterSelected else c.cluster
    Draw.hline p.x p.y (ctx.size.w - p.x.toNat) ' ' attr
    Draw.putStr p.x p.y icon attr
    Draw.putChar (p.x + 2) p.y (marker i) attr
    Draw.putHot (p.x + 5) p.y labels[i] attr c.clusterShortcut

def cursorPos (labels : Array HotText) (rows cursor : Nat) : Point :=
  itemPos labels rows cursor + ⟨2, 0⟩

/-- New cursor position after a navigation key, if it is one. -/
def navigate (n rows cursor : Nat) (k : Key) : Option Nat :=
  if n == 0 then none else
  let rows := max rows 1
  match k with
  | .up => some ((cursor + n - 1) % n)
  | .down => some ((cursor + 1) % n)
  | .left => some (if cursor ≥ rows then cursor - rows else cursor)
  | .right => some (if cursor + rows < n then cursor + rows else cursor)
  | _ => none

def hotkeyIndex? (labels : Array HotText) (c : Char) : Option Nat :=
  labels.findIdx? (·.hotkey? == some c)

end Cluster

/-- A group of independent on/off options. -/
structure CheckBoxes where
  items : Array (HotText × Bool)
  cursor : Nat := 0
deriving Inhabited

namespace CheckBoxes

def labels (cb : CheckBoxes) : Array HotText := cb.items.map (·.1)

def toggle (cb : CheckBoxes) (i : Nat) : CheckBoxes :=
  { cb with items := cb.items.modify i fun (t, v) => (t, !v), cursor := i }

def values (cb : CheckBoxes) : Array Bool := cb.items.map (·.2)

def handleKey (cb : CheckBoxes) (s : Size) (k : KeyEvent) : CheckBoxes × Reply :=
  if !k.mods.isNone && !(k.mods == { shift := true }) then (cb, .ignored) else
  match Cluster.navigate cb.items.size s.h cb.cursor k.key with
  | some i => ({ cb with cursor := i }, .handled)
  | none =>
    if k.key == .char ' ' then (cb.toggle cb.cursor, .handled)
    else match k.text? >>= fun ch => Cluster.hotkeyIndex? cb.labels ch.toLower with
      | some i => (cb.toggle i, .handled)
      | none => (cb, .ignored)

/-- A click toggles an item when pressed and released on it. -/
def handleMouse (cb : CheckBoxes) (s : Size) (m : MouseEvent) : CheckBoxes × Reply :=
  match m.action, Cluster.itemAt? cb.labels s.h m.pos with
  | .press, some i => ({ cb with cursor := i }, .handled)
  | .release, some i => if i == cb.cursor then (cb.toggle i, .handled) else (cb, .handled)
  | _, _ => (cb, .handled)

end CheckBoxes

instance : Widget CheckBoxes where
  draw cb ctx :=
    Cluster.draw cb.labels " [ ] " (fun i => if (cb.items[i]?.map (·.2)).getD false then 'X' else ' ')
      cb.cursor ctx
  handleKey := CheckBoxes.handleKey
  handleMouse := CheckBoxes.handleMouse
  hotkey cb c := (Cluster.hotkeyIndex? cb.labels c).map fun i => (cb.toggle i, .handled)
  cursor? cb s := some (Cluster.cursorPos cb.labels s.h cb.cursor)

/-- A group of mutually exclusive options. -/
structure RadioButtons where
  items : Array HotText
  selected : Nat := 0
deriving Inhabited

namespace RadioButtons

def handleKey (rb : RadioButtons) (s : Size) (k : KeyEvent) : RadioButtons × Reply :=
  if !k.mods.isNone && !(k.mods == { shift := true }) then (rb, .ignored) else
  match Cluster.navigate rb.items.size s.h rb.selected k.key with
  | some i => ({ rb with selected := i }, .handled)
  | none =>
    if k.key == .char ' ' then (rb, .handled)
    else match k.text? >>= fun ch => Cluster.hotkeyIndex? rb.items ch.toLower with
      | some i => ({ rb with selected := i }, .handled)
      | none => (rb, .ignored)

def handleMouse (rb : RadioButtons) (s : Size) (m : MouseEvent) : RadioButtons × Reply :=
  match m.action, Cluster.itemAt? rb.items s.h m.pos with
  | .press, some i => ({ rb with selected := i }, .handled)
  | _, _ => (rb, .handled)

end RadioButtons

instance : Widget RadioButtons where
  draw rb ctx :=
    Cluster.draw rb.items " ( ) " (fun i => if i == rb.selected then '•' else ' ') rb.selected ctx
  handleKey := RadioButtons.handleKey
  handleMouse := RadioButtons.handleMouse
  hotkey rb c := (Cluster.hotkeyIndex? rb.items c).map fun i => ({ rb with selected := i }, .handled)
  cursor? rb s := some (Cluster.cursorPos rb.items s.h rb.selected)

end HyperVision
