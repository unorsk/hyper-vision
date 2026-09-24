import HyperVision.Screen

/-!
# Hot-key text

Turbo Vision marks keyboard shortcuts with tildes: `"~F~ile"` renders `File` with
the `F` highlighted, and makes `Alt+F` (or `F` inside a menu) select it.
-/

namespace HyperVision

/-- A string split into plain and highlighted runs. -/
structure HotText where
  runs : Array (Bool × String)
deriving BEq, Inhabited, Repr

namespace HotText

/-- Parses `~`-delimited highlights: odd-numbered segments are highlighted. -/
def parse (s : String) : HotText :=
  let parts := (s.splitOn "~").toArray
  ⟨(parts.mapIdx fun i p => (i % 2 == 1, p)).filter (·.2 ≠ "")⟩

instance : Coe String HotText := ⟨parse⟩

/-- The text without markup. -/
def plain (t : HotText) : String := t.runs.foldl (· ++ ·.2) ""

def width (t : HotText) : Nat := t.plain.length

/-- The (lower-cased) shortcut character, if any. -/
def hotkey? (t : HotText) : Option Char := do
  let (_, s) ← t.runs.find? (·.1)
  let c ← s.toList.head?
  pure c.toLower

instance : ToString HotText := ⟨plain⟩

end HotText

namespace Draw

/-- Draws hot-key text, highlighted runs in `hi`, the rest in `normal`. -/
def putHot (x y : Int) (t : HotText) (normal hi : Attr) : DrawM Unit := do
  let mut cx := x
  for (isHot, s) in t.runs do
    putStr cx y s (if isHot then hi else normal)
    cx := cx + s.length

end Draw

/-- Pads or truncates a string to exactly `n` characters. -/
def fitString (s : String) (n : Nat) : String :=
  let cs := s.toList
  if cs.length ≥ n then String.ofList (cs.take n)
  else s.pushn ' ' (n - cs.length)

end HyperVision
