import HyperVision.Widget
import HyperVision.Terminal

/-!
# Text views

A read-only view of formatted text: paragraphs of styled spans, word-wrapped to the
view's width (with indentation and hanging indents), scrolled with the keyboard, the
mouse wheel or the scroll bar in the right-most column. Spans may be links: `Left` and
`Right` move between the links and `Enter` (or a click) activates the highlighted one,
which the view reports with `Reply.activated` — the owner reads the target back with
`TextView.linkTarget?`.

Wrapping depends on the width, which only the handlers and `draw` know. The handlers
cache the wrapped lines in the view; `draw` uses the cache when it has the right width
and wraps afresh otherwise.
-/

namespace HyperVision

/-- A run of text in one style. -/
structure TextSpan where
  text : String
  /-- Overrides the view's normal colors. -/
  attr : Option Attr := none
  /-- Makes the span (part of) a link to this target. Adjacent spans with the same
  target form a single link. -/
  link : Option String := none
deriving BEq, Repr, Inhabited

/-- A paragraph: spans laid out as running text. -/
structure TextPara where
  spans : Array TextSpan
  /-- Left margin of the paragraph, in columns. -/
  indent : Nat := 0
  /-- The first line starts this many columns left of `indent` (a hanging indent). -/
  hang : Nat := 0
  /-- Separated from the previous paragraph by a blank line. -/
  gapBefore : Bool := false
deriving BEq, Repr, Inhabited

/-- A piece of a wrapped line: text, colors and the number of the link it belongs to. -/
structure TextPiece where
  text : String
  attr : Option Attr
  link : Option Nat
deriving BEq, Repr, Inhabited

structure TextLine where
  indent : Nat
  pieces : Array TextPiece
deriving BEq, Repr, Inhabited

namespace TextLine

/-- The number of columns the line occupies. -/
def width (l : TextLine) : Nat :=
  l.indent + l.pieces.foldl (fun n p => n + p.text.foldl (fun n c => n + Terminal.charAdvance c) 0) 0

end TextLine

/-- The links of a document in order, numbered as `wrap` numbers them. -/
def TextPara.linkTargets (ps : Array TextPara) : Array String := Id.run do
  let mut out := #[]
  for p in ps do
    let mut prev : Option String := none
    for s in p.spans do
      if let some t := s.link then
        if prev != some t then out := out.push t
      prev := s.link
  return out

/-- Columns taken by `s` on the terminal (combining marks take none). -/
def textColumns (s : String) : Nat := s.foldl (fun n c => n + Terminal.charAdvance c) 0

/-- Breaks a paragraph into lines of at most `w` columns at spaces (words longer than a
line are cut). `firstLink` is the number of the paragraph's first link; the result
also returns the number after its last. -/
def wrapPara (w : Nat) (p : TextPara) (firstLink : Nat) : Array TextLine × Nat := Id.run do
  -- Number the links and split the spans into words (runs of non-spaces) and spaces.
  let mut link := firstLink
  let mut prev : Option String := none
  let mut words : Array (Bool × Array TextPiece) := #[] -- (is space, pieces)
  let mut cur : Array TextPiece := #[]
  for s in p.spans do
    let num := match s.link with
      | some t => if prev == some t then some (link - 1) else some link
      | none => none
    if s.link.isSome && prev != s.link then link := link + 1
    prev := s.link
    let parts := s.text.splitOn " "
    for h : k in [0:parts.length] do
      if k > 0 then
        if !cur.isEmpty then words := words.push (false, cur); cur := #[]
        words := words.push (true, #[{ text := " ", attr := s.attr, link := num }])
      let t := parts[k]
      if !t.isEmpty then cur := cur.push { text := t, attr := s.attr, link := num }
  if !cur.isEmpty then words := words.push (false, cur)
  -- In a narrow view, deep indentation would leave no room for the text.
  let indent := if p.indent + 10 > w then min p.indent (w / 3) else p.indent
  let hang := min p.hang indent
  let mut lines : Array TextLine := #[]
  let mut line : Array TextPiece := #[]
  let mut col := 0
  let mut lineIndent := indent - hang
  let mut avail := max 1 (w - lineIndent)
  let push (line : Array TextPiece) (pc : TextPiece) : Array TextPiece :=
    match line.back? with
    | some last =>
      if last.attr == pc.attr && last.link == pc.link then line.pop.push { last with text := last.text ++ pc.text }
      else line.push pc
    | none => line.push pc
  for (isSpace, pieces) in words do
    if isSpace then
      if col > 0 && col < avail then
        for pc in pieces do line := push line pc
        col := col + 1
      continue
    let wlen := pieces.foldl (fun n pc => n + textColumns pc.text) 0
    if col + wlen > avail && col > 0 then
      -- Start a new line, dropping the space the old one ended with.
      let line' := match line.back? with
        | some last => if last.text.endsWith " " then line.pop.push { last with text := (last.text.dropEnd 1).toString } else line
        | none => line
      lines := lines.push { indent := lineIndent, pieces := line'.filter (!·.text.isEmpty) }
      line := #[]
      col := 0
      lineIndent := indent
      avail := max 1 (w - indent)
    if wlen ≤ avail then
      for pc in pieces do line := push line pc
      col := col + wlen
    else
      for pc in pieces do
        for c in pc.text.toList do
          if col + Terminal.charAdvance c > avail then
            lines := lines.push { indent := lineIndent, pieces := line }
            line := #[]
            col := 0
            lineIndent := indent
            avail := max 1 (w - indent)
          line := push line { pc with text := String.singleton c }
          col := col + Terminal.charAdvance c
  if !line.isEmpty then lines := lines.push { indent := lineIndent, pieces := line }
  return (lines, link)

/-- Wraps paragraphs to `w` columns. -/
def wrapParas (ps : Array TextPara) (w : Nat) : Array TextLine := Id.run do
  let mut out := #[]
  let mut link := 0
  for p in ps do
    if p.gapBefore && !out.isEmpty then out := out.push { indent := 0, pieces := #[] }
    let (ls, next) := wrapPara w p link
    out := out ++ ls
    link := next
  return out

structure TextView where
  paras : Array TextPara := #[]
  /-- The first visible line. -/
  top : Nat := 0
  /-- The highlighted link, by number. -/
  link : Option Nat := none
  /-- Draw a scroll bar in the right-most column. -/
  scrollBar : Bool := true
  /-- Colors of unstyled text (the window's text colors by default). -/
  normal : Option Attr := none
  /-- The lines wrapped for `wrapWidth` columns (a cache; `none` when stale). -/
  wrapped : Option (Nat × Array TextLine) := none
  /-- While the button is held after a press on the scroll bar: whether it grabbed the thumb. -/
  scrollGrab : Option Bool := none
deriving Inhabited, Repr

namespace TextView

def ofParas (paras : Array TextPara) : TextView := { paras }

/-- Columns available for text at size `s`. -/
def textWidth (v : TextView) (s : Size) : Nat := if v.scrollBar then s.w - 1 else s.w

/-- The wrapped lines at size `s` (from the cache when it fits). -/
def lines (v : TextView) (s : Size) : Array TextLine :=
  match v.wrapped with
  | some (w, ls) => if w == v.textWidth s then ls else wrapParas v.paras (v.textWidth s)
  | none => wrapParas v.paras (v.textWidth s)

/-- Makes sure the cache holds the lines for size `s`. -/
def layout (v : TextView) (s : Size) : TextView :=
  match v.wrapped with
  | some (w, _) => if w == v.textWidth s then v else { v with wrapped := some (v.textWidth s, v.lines s) }
  | none => { v with wrapped := some (v.textWidth s, v.lines s) }

/-- Wraps for size `s` and scrolls back into the text if a resize left the view past its
end (as `ListBox.adjust` does). Handlers and `draw` start from the adjusted view. -/
def adjust (v : TextView) (s : Size) : TextView :=
  let v := v.layout s
  let m := (v.lines s).size - min (v.lines s).size s.h
  if v.top > m then { v with top := m } else v

/-- Replaces the text, scrolled to the top, with no link highlighted. -/
def setParas (v : TextView) (paras : Array TextPara) : TextView :=
  { v with paras, top := 0, link := none, wrapped := none, scrollGrab := none }

/-- Appends paragraphs, keeping the scroll position and the highlighted link (text
arriving in parts, such as the result of a background job). -/
def appendParas (v : TextView) (paras : Array TextPara) : TextView :=
  { v with paras := v.paras ++ paras, wrapped := none }

/-- The number of links. -/
def linkCount (v : TextView) : Nat := (TextPara.linkTargets v.paras).size

/-- The target of the highlighted link. -/
def linkTarget? (v : TextView) : Option String :=
  v.link.bind fun i => (TextPara.linkTargets v.paras)[i]?

def maxTop (v : TextView) (s : Size) : Nat := (v.lines s).size - min (v.lines s).size s.h

/-- Scrolls to line `t` (clamped). -/
def scrollTo (v : TextView) (s : Size) (t : Int) : TextView :=
  { v with top := (clampInt t 0 (v.maxTop s)).toNat }

/-- The line where paragraph `i` starts at size `s` (after its blank line, if any). -/
def paraLine (v : TextView) (s : Size) (i : Nat) : Nat :=
  let before := wrapParas (v.paras.extract 0 i) (v.textWidth s)
  let gap := match v.paras[i]? with
    | some p => if p.gapBefore && !before.isEmpty then 1 else 0
    | none => 0
  before.size + gap

/-- Scrolls so that paragraph `i` starts at the top of the view (as far as possible). -/
def scrollToPara (v : TextView) (s : Size) (i : Nat) : TextView :=
  let v := v.layout s
  v.scrollTo s (v.paraLine s i)

/-- The first line showing link `i`. -/
def lineOfLink (v : TextView) (s : Size) (i : Nat) : Option Nat :=
  (v.lines s).findIdx? fun l => l.pieces.any (·.link == some i)

/-- Highlights link `i` and scrolls it into view. -/
def focusLink (v : TextView) (s : Size) (i : Nat) : TextView :=
  match v.lineOfLink s i with
  | some row =>
    let v := { v with link := some i }
    if row < v.top then v.scrollTo s row
    else if row ≥ v.top + s.h then v.scrollTo s (row + 1 - s.h)
    else v
  | none => v

/-- The links shown on the visible lines. -/
def visibleLinks (v : TextView) (s : Size) : List Nat :=
  ((v.lines s).extract v.top (v.top + s.h)).toList.flatMap fun l => l.pieces.toList.filterMap (·.link)

/-- Moves the highlight to the next (or previous) link, starting from the visible ones. -/
def stepLink (v : TextView) (s : Size) (forward : Bool) : TextView :=
  let n := v.linkCount
  if n == 0 then v else
  let target := match v.link with
    | some i => if forward then (if i + 1 < n then some (i + 1) else none) else (if i > 0 then some (i - 1) else none)
    | none =>
      let vis := v.visibleLinks s
      if forward then vis.head? <|> some 0 else vis.getLast? <|> some (n - 1)
  match target with
  | some i => v.focusLink s i
  | none => v

/-- The vertical scroll bar. -/
def vBar (v : TextView) (s : Size) : ScrollBar :=
  { vertical := true, length := s.h, value := v.top, max := v.maxTop s }

/-- The link under the local position `p`, if any. -/
def linkAt? (v : TextView) (s : Size) (p : Point) : Option Nat := do
  guard (p.y ≥ 0 && p.x ≥ 0)
  let l ← (v.lines s)[v.top + p.y.toNat]?
  let mut x := l.indent
  for pc in l.pieces do
    let w := textColumns pc.text
    if x ≤ p.x.toNat && p.x.toNat < x + w then return (← pc.link)
    x := x + w
  none

def handleKey (v : TextView) (s : Size) (k : KeyEvent) : TextView × Reply :=
  let v := v.adjust s
  let page := max 1 (s.h - 1)
  if k.mods.alt then (v, .ignored) else
  match k.key with
  | .up => (v.scrollTo s (v.top - 1 : Int), .handled)
  | .down => (v.scrollTo s (v.top + 1), .handled)
  | .pageUp => (v.scrollTo s (v.top - page : Int), .handled)
  | .pageDown | .char ' ' => (v.scrollTo s (v.top + page), .handled)
  | .home => (v.scrollTo s 0, .handled)
  | .end => (v.scrollTo s (v.maxTop s), .handled)
  | .left => (v.stepLink s false, .handled)
  | .right => (v.stepLink s true, .handled)
  | .enter => if v.linkTarget?.isSome then (v, .activated) else (v, .ignored)
  | _ => (v, .ignored)

def handleMouse (v : TextView) (s : Size) (m : MouseEvent) : TextView × Reply :=
  let v := v.adjust s
  let p := m.pos
  let onBar := v.scrollBar && p.x == ((v.textWidth s : Nat) : Int) && 0 ≤ p.y && p.y < s.h
  match m.action with
  | .wheelUp => (v.scrollTo s (v.top - 3 : Int), .handled)
  | .wheelDown => (v.scrollTo s (v.top + 3), .handled)
  | .press =>
    if onBar then
      let sb := v.vBar s
      match sb.hit p.y.toNat with
      | .thumb => ({ v with scrollGrab := some true }, .handled)
      | part =>
        let delta : Int := match part with
          | .decArrow => -1 | .incArrow => 1 | .pageDec => -(max 1 (s.h - 1) : Nat) | _ => max 1 (s.h - 1)
        ({ v.scrollTo s (v.top + delta) with scrollGrab := some false }, .handled)
    else
      match v.linkAt? s p with
      | some i => ({ v with link := some i }, .activated)
      | none => (v, .handled)
  | .drag =>
    match v.scrollGrab with
    | some true => (v.scrollTo s ((v.vBar s).valueAt (clampInt p.y 0 (s.h - 1)).toNat), .handled)
    | _ => (v, .handled)
  | .release => ({ v with scrollGrab := none }, .handled)
  | .move => (v, .ignored)

def draw (v : TextView) (ctx : DrawCtx) : DrawM Unit := do
  let s := ctx.size
  let v := v.adjust s
  let normal := v.normal.getD (if ctx.inDialog then ctx.theme.dialog.staticText else ctx.window.text)
  let selected := if ctx.inDialog then ctx.theme.dialog.listFocused else ctx.window.selection
  let tw := v.textWidth s
  let ls := v.lines s
  for y in [0:s.h] do
    Draw.hline 0 y tw ' ' normal
    if let some l := ls[v.top + y]? then
      let mut x := l.indent
      for pc in l.pieces do
        let attr :=
          if ctx.focused && pc.link.isSome && pc.link == v.link then selected else pc.attr.getD normal
        for c in pc.text.toList do
          -- Zero-width characters cannot have a cell of their own.
          if Terminal.charAdvance c == 0 then continue
          if x < tw then Draw.putChar x y c attr
          x := x + Terminal.charAdvance c
  if v.scrollBar then
    let d := ctx.theme.dialog
    let (page, controls) := if ctx.inDialog then (d.scrollPage, d.scrollControls)
      else (ctx.window.scrollPage, ctx.window.scrollControls)
    (v.vBar s).draw tw 0 page controls

end TextView

instance : Widget TextView where
  draw := TextView.draw
  handleKey := TextView.handleKey
  handleMouse := TextView.handleMouse
  cancelMouse v := { v with scrollGrab := none }

end HyperVision
