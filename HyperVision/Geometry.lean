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
deriving DecidableEq, Repr, Inhabited, Hashable

namespace Point

instance : Add Point := ⟨fun a b => ⟨a.x + b.x, a.y + b.y⟩⟩
instance : Sub Point := ⟨fun a b => ⟨a.x - b.x, a.y - b.y⟩⟩

def origin : Point := ⟨0, 0⟩

@[simp] theorem add_x (a b : Point) : (a + b).x = a.x + b.x := rfl
@[simp] theorem add_y (a b : Point) : (a + b).y = a.y + b.y := rfl
@[simp] theorem sub_x (a b : Point) : (a - b).x = a.x - b.x := rfl
@[simp] theorem sub_y (a b : Point) : (a - b).y = a.y - b.y := rfl

end Point

/-- An axis-aligned rectangle: origin plus width and height. -/
structure Rect where
  x : Int
  y : Int
  w : Nat
  h : Nat
deriving DecidableEq, Repr, Inhabited

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

/-- `r` lies inside `r'`. -/
def Subset (r r' : Rect) : Prop := ∀ p, r.contains p → r'.contains p

theorem contains_iff {r : Rect} {p : Point} :
    r.contains p ↔ r.x ≤ p.x ∧ p.x < r.x + r.w ∧ r.y ≤ p.y ∧ p.y < r.y + r.h := by
  unfold contains right bottom
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- A point is in the intersection exactly when it is in both rectangles. -/
theorem contains_intersect {a b : Rect} {p : Point} :
    (a.intersect b).contains p ↔ a.contains p ∧ b.contains p := by
  simp only [contains_iff, intersect, right, bottom]
  omega

theorem contains_translate {r : Rect} {d p : Point} :
    (r.translate d).contains p ↔ r.contains (p - d) := by
  simp only [contains_iff, translate]
  show _ ↔ r.x ≤ p.x - d.x ∧ p.x - d.x < r.x + r.w ∧ r.y ≤ p.y - d.y ∧ p.y - d.y < r.y + r.h
  omega

theorem intersect_subset_left (a b : Rect) : (a.intersect b).Subset a :=
  fun _ h => (contains_intersect.1 h).1

theorem intersect_subset_right (a b : Rect) : (a.intersect b).Subset b :=
  fun _ h => (contains_intersect.1 h).2

end Rect

/-- Clamps `v` into `[lo, hi]` (returns `lo` when the range is empty). -/
def clampInt (v lo hi : Int) : Int := max lo (min v hi)

theorem clampInt_ge (v lo hi : Int) : lo ≤ clampInt v lo hi := by unfold clampInt; omega

theorem clampInt_le {v lo hi : Int} (h : lo ≤ hi) : clampInt v lo hi ≤ hi := by
  unfold clampInt; omega

theorem clampInt_of_mem {v lo hi : Int} (h₁ : lo ≤ v) (h₂ : v ≤ hi) : clampInt v lo hi = v := by
  unfold clampInt; omega

end HyperVision
