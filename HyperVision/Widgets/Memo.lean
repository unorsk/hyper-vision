import HyperVision.Widget

/-!
# Multi-line text

`Memo` is a small text editor (Turbo Vision's `TMemo`/`TEditor`): cursor movement,
shift/mouse selection, auto-indent, scrolling and an optional scroll bar.
-/

namespace HyperVision

/-- A position in a text: row and column, both 0-based. -/
structure TextPos where
  row : Nat
  col : Nat
deriving DecidableEq, Ord, Repr, Inhabited

namespace TextPos
/-- Document order (row first). -/
def le (a b : TextPos) : Bool := compare a b != .gt
end TextPos

abbrev Line := Array Char

structure Memo where
  lines : Array Line := #[#[]]
  cursor : TextPos := ⟨0, 0⟩
  /-- First visible row and column. -/
  top : Nat := 0
  left : Nat := 0
  /-- Selection anchor; the selection spans the anchor and the cursor. -/
  anchor : Option TextPos := none
  modified : Bool := false
  /-- Draw a vertical scroll bar in the rightmost column (memos inside dialogs). -/
  scrollBar : Bool := false
  /-- `Tab` inserts spaces instead of moving the focus to the next control. -/
  acceptsTab : Bool := false
  autoIndent : Bool := true
  /-- While the mouse button is held after a press on the scroll bar: whether it grabbed the thumb. -/
  scrollGrab : Option Bool := none
deriving Inhabited, Repr

namespace Memo

def ofString (s : String) : Memo :=
  { lines := (s.toList.splitOn '\n').toArray.map List.toArray }

def text (m : Memo) : String :=
  String.ofList (['\n'].intercalate (m.lines.toList.map (·.toList)))

def line (m : Memo) (r : Nat) : Line := m.lines[r]?.getD #[]

def lastRow (m : Memo) : Nat := m.lines.size - 1

def clampPos (m : Memo) (p : TextPos) : TextPos :=
  let row := min p.row m.lastRow
  ⟨row, min p.col (m.line row).size⟩

/-- The text area (excluding the scroll bar). -/
def textSize (m : Memo) (s : Size) : Size := if m.scrollBar then ⟨s.w - 1, s.h⟩ else s

def maxLineLength (m : Memo) : Nat := m.lines.foldl (max · ·.size) 0

/-- Scrolls so the cursor is visible. -/
def adjust (m : Memo) (s : Size) : Memo :=
  let ts := m.textSize s
  let c := m.clampPos m.cursor
  let h := max ts.h 1
  let w := max ts.w 1
  let top := if c.row < m.top then c.row else if c.row ≥ m.top + h then c.row + 1 - h else m.top
  let left := if c.col < m.left then c.col else if c.col ≥ m.left + w then c.col + 1 - w else m.left
  { m with cursor := c, top, left }

/-- The ordered selection, if non-empty. -/
def selection? (m : Memo) : Option (TextPos × TextPos) :=
  m.anchor.bind fun a =>
    if a == m.cursor then none
    else if a.le m.cursor then some (a, m.cursor) else some (m.cursor, a)

def isSelected (m : Memo) (p : TextPos) : Bool :=
  match m.selection? with
  | some (lo, hi) => lo.le p && !hi.le p
  | none => false

/-- Deletes the text between `a` and `b` (with `a ≤ b`) and puts the cursor at `a`. -/
def deleteRange (m : Memo) (a b : TextPos) : Memo :=
  let joined := (m.line a.row).extract 0 a.col ++ (m.line b.row).extract b.col (m.line b.row).size
  { m with
    lines := m.lines.extract 0 a.row |>.push joined |>.append (m.lines.extract (b.row + 1) m.lines.size)
    cursor := a, anchor := none, modified := true }

def deleteSelection (m : Memo) : Memo :=
  match m.selection? with
  | some (lo, hi) => m.deleteRange lo hi
  | none => { m with anchor := none }

def insertChars (m : Memo) (cs : Array Char) : Memo :=
  let m := m.deleteSelection
  let c := m.clampPos m.cursor
  let l := m.line c.row
  let l' := l.extract 0 c.col ++ cs ++ l.extract c.col l.size
  let lines := if m.lines.isEmpty then #[l'] else m.lines.setIfInBounds c.row l'
  { m with lines, cursor := ⟨c.row, c.col + cs.size⟩, modified := true }

def newline (m : Memo) : Memo :=
  let m := m.deleteSelection
  let c := m.clampPos m.cursor
  let l := m.line c.row
  let indent := if m.autoIndent then (l.toList.takeWhile (· == ' ')).length else 0
  let before := l.extract 0 c.col
  let after := Array.replicate (min indent c.col) ' ' ++ l.extract c.col l.size
  { m with
    lines := m.lines.extract 0 c.row |>.push before |>.push after
      |>.append (m.lines.extract (c.row + 1) m.lines.size)
    cursor := ⟨c.row + 1, min indent c.col⟩, modified := true }

/-- Inserts text that may span several lines (without auto-indent). -/
def insertText (m : Memo) (s : String) : Memo :=
  let indent := m.autoIndent
  let (m, _) := (s.toList.splitOn '\n').foldl (init := ({ m with autoIndent := false }, true))
    fun (m, first) part =>
      let m := if first then m else m.newline
      (m.insertChars part.toArray, false)
  { m with autoIndent := indent }

def backspace (m : Memo) : Memo :=
  if m.selection?.isSome then m.deleteSelection else
  let c := m.clampPos m.cursor
  if c.col > 0 then m.deleteRange ⟨c.row, c.col - 1⟩ c
  else if c.row > 0 then m.deleteRange ⟨c.row - 1, (m.line (c.row - 1)).size⟩ c
  else m

def deleteForward (m : Memo) : Memo :=
  if m.selection?.isSome then m.deleteSelection else
  let c := m.clampPos m.cursor
  if c.col < (m.line c.row).size then m.deleteRange c ⟨c.row, c.col + 1⟩
  else if c.row < m.lastRow then m.deleteRange c ⟨c.row + 1, 0⟩
  else m

private def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

def wordLeft (m : Memo) (p : TextPos) : TextPos :=
  if p.col == 0 then (if p.row == 0 then p else ⟨p.row - 1, (m.line (p.row - 1)).size⟩) else
  let l := (m.line p.row).extract 0 p.col |>.toList.reverse
  let skipSpace := (l.takeWhile (!isWordChar ·)).length
  let word := ((l.drop skipSpace).takeWhile isWordChar).length
  ⟨p.row, p.col - skipSpace - word⟩

def wordRight (m : Memo) (p : TextPos) : TextPos :=
  let l := m.line p.row
  if p.col ≥ l.size then (if p.row < m.lastRow then ⟨p.row + 1, 0⟩ else p) else
  let rest := (l.extract p.col l.size).toList
  let word := (rest.takeWhile isWordChar).length
  let space := ((rest.drop word).takeWhile (!isWordChar ·)).length
  ⟨p.row, p.col + max 1 (word + space)⟩

/-- Moves the cursor, extending the selection when `extend` is set. -/
def moveTo (m : Memo) (p : TextPos) (extend : Bool) : Memo :=
  let p := m.clampPos p
  if extend then { m with anchor := some (m.anchor.getD m.cursor), cursor := p }
  else { m with anchor := none, cursor := p }

def target (m : Memo) (s : Size) (k : KeyEvent) : Option TextPos :=
  let c := m.clampPos m.cursor
  let page := max 1 ((m.textSize s).h - 1)
  match k.key with
  | .left => some <|
      if k.mods.ctrl then m.wordLeft c
      else if c.col > 0 then ⟨c.row, c.col - 1⟩
      else if c.row > 0 then ⟨c.row - 1, (m.line (c.row - 1)).size⟩ else c
  | .right => some <|
      if k.mods.ctrl then m.wordRight c
      else if c.col < (m.line c.row).size then ⟨c.row, c.col + 1⟩
      else if c.row < m.lastRow then ⟨c.row + 1, 0⟩ else c
  | .up => some ⟨c.row - 1, m.cursor.col⟩
  | .down => some ⟨c.row + 1, m.cursor.col⟩
  | .home => some (if k.mods.ctrl then ⟨0, 0⟩ else ⟨c.row, 0⟩)
  | .end => some (if k.mods.ctrl then ⟨m.lastRow, (m.line m.lastRow).size⟩
      else ⟨c.row, (m.line c.row).size⟩)
  | .pageUp => some ⟨c.row - page, c.col⟩
  | .pageDown => some ⟨c.row + page, c.col⟩
  | _ => none

def handleKey (m : Memo) (s : Size) (k : KeyEvent) : Memo × Reply :=
  let edited : Option Memo :=
    match m.target s k with
    | some p =>
      -- Page keys scroll the view along with the cursor.
      let m' := m.moveTo p k.mods.shift
      let ts := m.textSize s
      let page := max 1 (ts.h - 1)
      let maxTop := m.lines.size - min m.lines.size ts.h
      some <| match k.key with
        | .pageUp => { m' with top := m.top - page }
        | .pageDown => { m' with top := min (m.top + page) maxTop }
        | _ => m'
    | none =>
      match k.key with
      | .enter => if k.mods.isNone then some m.newline else none
      | .backspace => some m.backspace
      | .delete => some m.deleteForward
      | .tab =>
        if m.acceptsTab && k.mods.isNone then
          let m := m.deleteSelection
          some (m.insertChars (Array.replicate (4 - (m.clampPos m.cursor).col % 4) ' '))
        else none
      | .char 'a' =>
        if k.mods.ctrl then
          some { m with anchor := some ⟨0, 0⟩, cursor := ⟨m.lastRow, (m.line m.lastRow).size⟩ }
        else k.text?.map fun ch => m.insertChars #[ch]
      | _ => k.text?.map fun ch => m.insertChars #[ch]
  match edited with
  | some m' => (m'.adjust s, .handled)
  | none => (m, .ignored)

/-- The vertical scroll bar for a view of height `h`. -/
def vBar (m : Memo) (h : Nat) (length : Nat) : ScrollBar :=
  { vertical := true, length, value := m.top, max := m.lines.size - min m.lines.size h }

/-- The horizontal scroll bar for a view of width `w`. -/
def hBar (m : Memo) (w : Nat) (length : Nat) : ScrollBar :=
  { vertical := false, length, value := m.left, max := m.maxLineLength + 1 - min (m.maxLineLength + 1) w }

def scrollBy (m : Memo) (s : Size) (dy dx : Int) : Memo :=
  let ts := m.textSize s
  let maxTop := m.lines.size - min m.lines.size ts.h
  let maxLeft := m.maxLineLength + 1 - min (m.maxLineLength + 1) ts.w
  { m with top := (clampInt (m.top + dy) 0 maxTop).toNat
           left := (clampInt (m.left + dx) 0 maxLeft).toNat }

/-- Scrolls so that the scroll bar shows `value`. -/
def scrollToValue (m : Memo) (s : Size) (vertical : Bool) (value : Nat) : Memo :=
  if vertical then m.scrollBy s ((value : Int) - m.top) 0 else m.scrollBy s 0 ((value : Int) - m.left)

/-- Applies a click on a scroll bar part. -/
def scrollPart (m : Memo) (s : Size) (vertical : Bool) (sb : ScrollBar) (offset : Nat) : Memo :=
  let ts := m.textSize s
  let page : Int := if vertical then max 1 (ts.h - 1) else max 1 (ts.w - 1)
  let delta : Int := match sb.hit offset with
    | .decArrow => -1 | .incArrow => 1 | .pageDec => -page | .pageInc => page | .thumb => 0
  let delta := if sb.hit offset == .thumb then (sb.valueAt offset : Int) - sb.value else delta
  if vertical then m.scrollBy s delta 0 else m.scrollBy s 0 delta

def handleMouse (m : Memo) (s : Size) (e : MouseEvent) : Memo × Reply :=
  let ts := m.textSize s
  match e.action with
  | .wheelUp => (m.scrollBy s (-3) 0, .handled)
  | .wheelDown => (m.scrollBy s 3 0, .handled)
  | .release => ({ m with scrollGrab := none }, .handled)
  | .press | .drag =>
    let sb := m.vBar ts.h s.h
    let off := (clampInt e.pos.y 0 (s.h - 1)).toNat
    match e.action, m.scrollGrab with
    | .drag, some true => (m.scrollToValue s true (sb.valueAt off), .handled)
    | .drag, some false => (m, .handled)
    | _, _ =>
    if e.action == .press && m.scrollBar && e.pos.x == ts.w then
      let thumb := sb.hit off == .thumb
      let m := { m with scrollGrab := some thumb }
      (if thumb then m else m.scrollPart s true sb off, .handled)
    else
      -- Dragging past the edges scrolls the text.
      let m := if e.action == .drag then
          m.scrollBy s (if e.pos.y < 0 then -1 else if e.pos.y ≥ ts.h then 1 else 0)
            (if e.pos.x < 0 then -1 else if e.pos.x ≥ ts.w then 1 else 0)
        else m
      let row := (clampInt (m.top + e.pos.y) 0 m.lastRow).toNat
      let col := (clampInt (m.left + e.pos.x) 0 (m.line row).size).toNat
      let m' := m.moveTo ⟨row, col⟩ (e.action == .drag)
      (m', .handled)
  | _ => (m, .handled)

/-- Colors: those of the list viewer in dialogs, of the window class otherwise. -/
def colors (ctx : DrawCtx) : Attr × Attr :=
  if ctx.inDialog then (ctx.theme.dialog.listNormal, ctx.theme.dialog.listFocused)
  else (ctx.window.text, ctx.window.selection)

def draw (m : Memo) (ctx : DrawCtx) : DrawM Unit := do
  let (normal, selected) := colors ctx
  let ts := m.textSize ctx.size
  for y in [0:ts.h] do
    let row := m.top + y
    Draw.hline 0 y ts.w ' ' normal
    let l := m.line row
    for x in [0:ts.w] do
      let col := m.left + x
      let sel := m.isSelected ⟨row, col⟩ && (col < l.size || row < m.lastRow && col == l.size)
      if h : col < l.size then
        Draw.putChar x y l[col] (if sel then selected else normal)
      else if sel then Draw.putChar x y ' ' selected
  if m.scrollBar then
    let d := ctx.theme.dialog
    (m.vBar ts.h ctx.size.h).draw ts.w 0 d.scrollPage d.scrollControls

end Memo

instance : Widget Memo where
  draw := Memo.draw
  handleKey := Memo.handleKey
  handleMouse := Memo.handleMouse
  cursor? m s :=
    let c := m.clampPos m.cursor
    let ts := m.textSize s
    if m.top ≤ c.row && c.row < m.top + ts.h && m.left ≤ c.col && c.col < m.left + ts.w then
      some ⟨c.col - m.left, c.row - m.top⟩
    else none
  wantsText _ := true
  cancelMouse m := { m with scrollGrab := none }

end HyperVision
