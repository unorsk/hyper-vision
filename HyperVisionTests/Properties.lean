import HyperVisionTests.Oracles

/-!
# Property tests

Randomized tests (Plausible) for properties that complement the proofs: they
exercise the parts that are specified by external conventions (xterm encodings,
ANSI output) against independent oracles, and check geometric and editing
behaviour against simple reference models. A counterexample fails the build.
-/

namespace HyperVisionTests

open HyperVision Plausible Input

def cfg : Configuration := { numInst := 400, quiet := true }

/-! ## Input decoding against the xterm encoder -/

-- Every key press xterm can send decodes to exactly that key press.
#eval Testable.check
  (∀ k : KeyEvent, decodeList false ((encodeKey k).getD []) = ([.key k], [])) cfg

-- Every SGR mouse report decodes to exactly that mouse event.
#eval Testable.check
  (∀ m : MouseEvent, decodeList false ((encodeMouse m).getD []) = ([.mouse m], [])) cfg

-- A stream of events decodes to the same events, in order, with nothing left over.
#eval Testable.check
  (∀ evs : List Event,
    decodeList false (evs.flatMap fun e => (encodeEvent e).getD []) = (evs, [])) cfg

-- Splitting that stream at any byte and feeding it in two reads changes nothing.
#eval Testable.check
  (∀ (evs : List Event) (cut : Nat),
    let bs := evs.flatMap fun e => (encodeEvent e).getD []
    [bs.take cut, bs.drop cut].foldl feed ([], []) = (evs, [])) cfg

/-! ## Rendering against the ANSI model terminal -/

-- Playing the diff output on a terminal that shows the previous frame yields the next.
#eval Testable.check
  (∀ p : ScreenPair,
    let t : TermModel := ⟨p.prev.map Terminal.Cell.shown, 0, 0, ⟨.white, .blue⟩⟩
    (interpret t (Terminal.diff .trueColor (some p.prev) p.next none)).grid.cells =
      (p.next.map Terminal.Cell.shown).cells) cfg

-- A full repaint yields the frame whatever the terminal showed before.
#eval Testable.check
  (∀ p : ScreenPair,
    let t : TermModel := ⟨p.prev, 3, 1, ⟨.red, .green⟩⟩
    (interpret t (Terminal.diff .trueColor none p.next none)).grid.cells =
      (p.next.map Terminal.Cell.shown).cells) cfg

/-! ## Window management geometry -/

def overlap (a b : Rect) : Bool :=
  a.x < b.right && b.x < a.right && a.y < b.bottom && b.y < a.bottom

def within (a desk : Rect) : Bool :=
  desk.x ≤ a.x && a.right ≤ desk.right && desk.y ≤ a.y && a.bottom ≤ desk.bottom

def desktopOf (n w h : Nat) : Desktop Unit :=
  (List.range n).foldl (init := ({ bounds := ⟨0, 1, w, h⟩ } : Desktop Unit)) fun d _ =>
    d.insert { Window.new "w" ⟨0, 1, 10, 5⟩ with minSize := ⟨1, 1⟩ }

-- Tiling covers the desktop exactly: every tile inside it, no overlaps, no gaps. -/
-- def tileExact (n w h : Nat) : Bool :=
-- let d := desktopOf n w h
-- let rs := d.tile.windows.toList.map (·.bounds)
-- rs.all (within · d.bounds) &&
-- (rs.zipIdx.all fun (a, i) => rs.zipIdx.all fun (b, j) => i == j || !overlap a b) &&
-- (rs.foldl (fun acc r => acc + r.w * r.h) 0 == w * h)
-- 
-- #eval Testable.check (∀ n w h : Nat, tileExact (n % 16 + 1) (w % 180 + 20) (h % 55 + 5) = true) cfg
-- 
-- /-- Cascading keeps every window inside the desktop.
#eval Testable.check
  (∀ n w h : Nat,
    let d := desktopOf (n % 16 + 1) (w % 180 + 20) (h % 55 + 17)
    d.cascade.windows.all (within ·.bounds d.bounds) = true) cfg

/-! ## Drawing agrees with hit-testing -/

/-- The close icon, zoom icon and resize corner are drawn exactly where (and only when)
the frame reacts to them. -/
def iconsAgree (w : Window Unit) : Bool :=
  let scr := Draw.run (Screen.new w.bounds.w w.bounds.h)
    (Draw.within w.bounds (w.draw Theme.turboVision true false))
  let ch (x y : Int) : Char := ((scr.get? x y).map (·.ch)).getD '?'
  let wd : Int := w.bounds.w
  let ht : Int := w.bounds.h
  ((w.frameHit ⟨3, 0⟩ == .close) == w.flags.close) && ((ch 3 0 == '■') == w.flags.close) &&
  ((w.frameHit ⟨wd - 4, 0⟩ == .zoom) == w.flags.zoom) && ((ch (wd - 4) 0 == '↑') == w.flags.zoom) &&
  ((w.frameHit ⟨wd - 1, ht - 1⟩ == .resize) == w.flags.grow) &&
    ((ch (wd - 1) (ht - 1) == '┘') == w.flags.grow)

#eval Testable.check (∀ w : Window Unit, iconsAgree w = true) cfg

/-! ## Editing against reference models -/

inductive EditOp where
  | ins (c : Char) | enter | bs | del | left | right | home | «end»
deriving Repr, Inhabited

instance : Arbitrary EditOp := ⟨do
  match ← natIn 0 9 with
  | 0 | 1 | 2 => pure (.ins (Char.ofNat (← natIn 32 126)))
  | 3 => pure .enter | 4 => pure .bs | 5 => pure .del | 6 => pure .left | 7 => pure .right
  | 8 => pure .home | _ => pure .end⟩
instance : Shrinkable EditOp := {}

def EditOp.key : EditOp → KeyEvent
  | .ins c => .plain (.char c) | .enter => .plain .enter | .bs => .plain .backspace
  | .del => .plain .delete | .left => .plain .left | .right => .plain .right
  | .home => .plain .home | .end => .plain .end

/-- A text with a cursor, as a flat character list. -/
structure TextModel where
  text : List Char
  cur : Nat

/-- Reference semantics of an edit on a single line of at most `max` characters. -/
def TextModel.applyLine (m : TextModel) (max : Nat) : EditOp → TextModel
  | .ins c => if m.text.length < max then ⟨m.text.take m.cur ++ c :: m.text.drop m.cur, m.cur + 1⟩ else m
  | .bs => if m.cur > 0 then ⟨m.text.eraseIdx (m.cur - 1), m.cur - 1⟩ else m
  | .del => if m.cur < m.text.length then ⟨m.text.eraseIdx m.cur, m.cur⟩ else m
  | .left => ⟨m.text, m.cur - 1⟩
  | .right => ⟨m.text, min (m.cur + 1) m.text.length⟩
  | .home => ⟨m.text, 0⟩
  | .end => ⟨m.text, m.text.length⟩
  | .enter => m

/-- An input line behaves like the reference model (and never exceeds its maximum). -/
def inputLineAgrees (ops : List EditOp) : Bool :=
  let max := 12
  let step := fun ((i, m) : InputLine × TextModel) (op : EditOp) =>
    ((i.handleKey ⟨20, 1⟩ op.key).1, m.applyLine max op)
  let states := ops.scanl step (InputLine.ofString "" max, ⟨[], 0⟩)
  states.all fun (i, m) => i.text.toList == m.text && i.cursor == m.cur && i.text.size ≤ max

#eval Testable.check (∀ ops : List EditOp, inputLineAgrees ops = true) cfg

/-- Start of the line containing offset `cur`. -/
def lineStart (t : List Char) (cur : Nat) : Nat :=
  ((List.range cur).filter fun k => t[k]? == some '\n').foldl (fun _ k => k + 1) 0

/-- End of the line containing offset `cur`. -/
def lineEnd (t : List Char) (cur : Nat) : Nat :=
  ((List.range (t.length - cur)).find? fun k => t[cur + k]? == some '\n').map (cur + ·) |>.getD t.length

/-- Reference semantics of an edit on a multi-line text. -/
def TextModel.applyText (m : TextModel) : EditOp → TextModel
  | .ins c => ⟨m.text.take m.cur ++ c :: m.text.drop m.cur, m.cur + 1⟩
  | .enter => ⟨m.text.take m.cur ++ '\n' :: m.text.drop m.cur, m.cur + 1⟩
  | .bs => if m.cur > 0 then ⟨m.text.eraseIdx (m.cur - 1), m.cur - 1⟩ else m
  | .del => if m.cur < m.text.length then ⟨m.text.eraseIdx m.cur, m.cur⟩ else m
  | .left => ⟨m.text, m.cur - 1⟩
  | .right => ⟨m.text, min (m.cur + 1) m.text.length⟩
  | .home => ⟨m.text, lineStart m.text m.cur⟩
  | .end => ⟨m.text, lineEnd m.text m.cur⟩

/-- The memo cursor as an offset into its text. -/
def memoOffset (m : Memo) : Nat :=
  ((m.lines.extract 0 m.cursor.row).foldl (fun acc l => acc + l.size + 1) 0) + m.cursor.col

/-- A memo behaves like the reference model of a flat text with a cursor. -/
def memoAgrees (ops : List EditOp) : Bool :=
  let step := fun ((me, m) : Memo × TextModel) (op : EditOp) =>
    ((me.handleKey ⟨30, 8⟩ op.key).1, m.applyText op)
  let states := ops.scanl step ({ Memo.ofString "" with autoIndent := false }, ⟨[], 0⟩)
  states.all fun (me, m) => me.text.toList == m.text && memoOffset me == m.cur

#eval Testable.check (∀ ops : List EditOp, memoAgrees ops = true) cfg

end HyperVisionTests
