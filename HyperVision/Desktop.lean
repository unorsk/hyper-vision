import HyperVision.Window

/-!
# Desktop

The stack of windows between the menu bar and the status line. The last window
is the front-most and active one. Placement follows Turbo Vision: windows can be
dragged partially off the desktop but never above it, and `tile`/`cascade` use
the original layout algorithms.
-/

namespace HyperVision

structure Desktop (α : Type) where
  /-- Back to front: the last window is active. -/
  windows : Array (Window α) := #[]
  nextId : Nat := 1
  /-- The area windows live in, in screen coordinates. -/
  bounds : Rect
deriving Inhabited

namespace Desktop

variable {α : Type}

def top? (d : Desktop α) : Option (Window α) := d.windows.back?

def indexOf? (d : Desktop α) (id : Nat) : Option Nat := d.windows.findIdx? (·.id == id)

def find? (d : Desktop α) (id : Nat) : Option (Window α) := d.windows.find? (·.id == id)

def modify (d : Desktop α) (id : Nat) (f : Window α → Window α) : Desktop α :=
  match d.indexOf? id with
  | some i => { d with windows := d.windows.modify i f }
  | none => d

/-- Whether the front window is modal (and so blocks everything else). -/
def modalActive (d : Desktop α) : Bool := d.top?.any (·.modal)

/-- The lowest window number (1‥9) not in use. -/
def freeNumber (d : Desktop α) : Option Nat :=
  (List.range' 1 9).find? fun n => !d.windows.any (·.number == some n)

/-- Adds a window in front and returns its id. Plain windows get a free number. -/
def insert' (d : Desktop α) (w : Window α) : Desktop α × Nat :=
  let number := if w.isDialog || w.number.isSome then w.number else d.freeNumber
  -- As in `TWindow`'s constructor, un-zooming restores the initial bounds.
  let w := { w with id := d.nextId, number, zoomRect := w.zoomRect <|> some w.bounds }.initFocus
  ({ d with windows := d.windows.push w, nextId := d.nextId + 1 }, w.id)

def insert (d : Desktop α) (w : Window α) : Desktop α := (d.insert' w).1

/-- Adds a window centered on the desktop. -/
def insertCentered (d : Desktop α) (w : Window α) : Desktop α :=
  let x := d.bounds.x + ((d.bounds.w : Int) - w.bounds.w) / 2
  let y := d.bounds.y + ((d.bounds.h : Int) - w.bounds.h) / 2
  d.insert { w with bounds := { w.bounds with x, y := max d.bounds.y y } }

def close (d : Desktop α) (id : Nat) : Desktop α :=
  { d with windows := d.windows.filter (·.id != id) }

/-- Brings a window to the front. -/
def raise (d : Desktop α) (id : Nat) : Desktop α :=
  match d.find? id with
  | some w => { d with windows := (d.windows.filter (·.id != id)).push w }
  | none => d

/-- The back-most window comes to the front (Turbo Vision's `cmNext`). -/
def next (d : Desktop α) : Desktop α :=
  if d.modalActive then d else
  match d.windows[0]? with
  | some w => { d with windows := (d.windows.extract 1 d.windows.size).push w }
  | none => d

/-- The front window goes to the back (`cmPrev`). -/
def prev (d : Desktop α) : Desktop α :=
  if d.modalActive then d else
  match d.windows.back? with
  | some w => { d with windows := #[w] ++ d.windows.pop }
  | none => d

/-- Selects the window showing number `n` (`Alt+n`). -/
def selectNumber (d : Desktop α) (n : Nat) : Desktop α :=
  if d.modalActive then d else
  match d.windows.find? (·.number == some n) with
  | some w => d.raise w.id
  | none => d

/-- Constrains a window origin: never above the desktop, and at least one column visible. -/
def constrain (d : Desktop α) (s : Size) (p : Point) : Point :=
  let l := d.bounds
  ⟨clampInt p.x (l.x - s.w + 1) (l.right - 1), clampInt p.y l.y (l.bottom - 1)⟩

def moveTo (d : Desktop α) (id : Nat) (p : Point) : Desktop α :=
  d.modify id fun w =>
    let p := d.constrain w.size p
    { w with bounds := { w.bounds with x := p.x, y := p.y } }

/-- Resizes a window keeping its origin, within its minimum size and the desktop size. -/
def resizeTo (d : Desktop α) (id : Nat) (s : Size) : Desktop α :=
  d.modify id fun w =>
    let wd := max w.minSize.w (min s.w d.bounds.w)
    let ht := max w.minSize.h (min s.h d.bounds.h)
    w.setBounds { w.bounds with w := wd, h := ht }

/-- Zooms a window to the whole desktop, or restores it if it already has that size. -/
def toggleZoom (d : Desktop α) (id : Nat) : Desktop α :=
  d.modify id fun w =>
    if !w.flags.zoom then w
    else if w.isMaximized d.bounds then (w.zoomRect.map w.setBounds).getD w
    else { w.setBounds d.bounds with zoomRect := some w.bounds }

private def tileable (w : Window α) : Bool := !w.isDialog && !w.modal

/-- Turbo Vision's `mostEqualDivisors`: columns and rows for `n` tiles. -/
def mostEqualDivisors (n : Nat) : Nat × Nat :=
  let s := (List.range (n + 1)).foldl (fun acc k => if k * k ≤ n then k else acc) 1
  let i := if n % s != 0 && n % (s + 1) == 0 then s + 1 else s
  let i := if i < n / i then n / i else i
  (i, n / i)

private def dividerLoc (lo : Int) (len num pos : Nat) : Int := lo + (len * pos / num : Nat)

/-- Places each window at its rectangle, unless one would be below its minimum size
(Turbo Vision refuses such a layout with `tileError`). -/
def arrange (d : Desktop α) (layout : Array (Window α × Rect)) : Desktop α :=
  if layout.any fun (w, r) => r.w < w.minSize.w || r.h < w.minSize.h then d
  else layout.foldl (fun d (w, r) => d.modify w.id (·.setBounds r)) d

/-- Tiles the plain windows over the desktop, front-most at the bottom-right. -/
def tile (d : Desktop α) : Desktop α :=
  let ws := d.windows.filter tileable
  let n := ws.size
  let (cols, rows) := mostEqualDivisors n
  let r := d.bounds
  if n == 0 || cols == 0 || rows == 0 then d else
  let leftOver := n % cols
  let split := (cols - leftOver) * rows
  d.arrange <| ws.mapIdx fun k w =>
    let (cx, cy, rowsHere) :=
      if k < split then (k / rows, k % rows, rows)
      else ((k - split) / (rows + 1) + (cols - leftOver), (k - split) % (rows + 1), rows + 1)
    let x0 := dividerLoc r.x r.w cols cx
    let x1 := dividerLoc r.x r.w cols (cx + 1)
    let y0 := dividerLoc r.y r.h rowsHere cy
    let y1 := dividerLoc r.y r.h rowsHere (cy + 1)
    (w, ⟨x0, y0, (x1 - x0).toNat, (y1 - y0).toNat⟩)

/-- Cascades the plain windows, each offset one cell from the one behind it. -/
def cascade (d : Desktop α) : Desktop α :=
  let r := d.bounds
  d.arrange <| (d.windows.filter tileable).mapIdx fun k w => (w, ⟨r.x + k, r.y + k, r.w - k, r.h - k⟩)

/-- Adapts to a new desktop area (terminal resize). -/
def setBounds (d : Desktop α) (r : Rect) : Desktop α :=
  let old := d.bounds
  let d := { d with bounds := r }
  { d with windows := d.windows.map fun w =>
      if w.isMaximized old then w.setBounds r
      else
        let p := d.constrain w.size w.bounds.origin
        { w with bounds := { w.bounds with x := p.x, y := p.y } } }

end Desktop

end HyperVision
