/-!
# Geometry

Points and rectangles in character-cell coordinates. Coordinates are `Int` because
windows may be dragged partially off-screen; extents are `Nat`.
-/

namespace HyperVision

/-- A position in character cells. -/
structure Point where
  x : Int
  y : Int
deriving BEq, DecidableEq, Repr, Inhabited, Hashable

namespace Point

instance : Add Point := ⟨fun a b => ⟨a.x + b.x, a.y + b.y⟩⟩
instance : Sub Point := ⟨fun a b => ⟨a.x - b.x, a.y - b.y⟩⟩

def origin : Point := ⟨0, 0⟩

end Point

/-- An axis-aligned rectangle: origin plus width and height. -/
structure Rect where
  x : Int
  y : Int
  w : Nat
  h : Nat
deriving BEq, DecidableEq, Repr, Inhabited

namespace Rect

def origin (r : Rect) : Point := ⟨r.x, r.y⟩

/-- One past the right-most column. -/
def right (r : Rect) : Int := r.x + r.w

/-- One past the bottom-most row. -/
def bottom (r : Rect) : Int := r.y + r.h

def isEmpty (r : Rect) : Bool := r.w == 0 || r.h == 0

def contains (r : Rect) (p : Point) : Bool :=
  r.x ≤ p.x && p.x < r.right && r.y ≤ p.y && p.y < r.bottom

def translate (r : Rect) (d : Point) : Rect := { r with x := r.x + d.x, y := r.y + d.y }

/-- Shrinks the rectangle by `n` cells on every side. -/
def inset (r : Rect) (n : Nat) : Rect :=
  ⟨r.x + n, r.y + n, r.w - 2 * n, r.h - 2 * n⟩

def intersect (a b : Rect) : Rect :=
  let x0 := max a.x b.x
  let y0 := max a.y b.y
  let x1 := min a.right b.right
  let y1 := min a.bottom b.bottom
  ⟨x0, y0, (x1 - x0).toNat, (y1 - y0).toNat⟩

/-- Converts a point to coordinates relative to the rectangle's origin. -/
def toLocal (r : Rect) (p : Point) : Point := p - r.origin

end Rect

/-- Clamps `v` into `[lo, hi]` (returns `lo` when the range is empty). -/
def clampInt (v lo hi : Int) : Int := max lo (min v hi)

end HyperVision
