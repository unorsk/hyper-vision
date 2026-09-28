import HyperVision.Widget

/-!
# File lists

The pure parts of Turbo Vision's file dialog (`TFileDialog`):

* `FileEntry`, a directory entry, and the order `TFileCollection` sorts entries in;
* wildcard matching (`*`, `?`, and several patterns separated by `;`);
* `FileList` (`TFileList`): the sorted entries in two columns, with type-ahead search
  and a scroll bar along the bottom row that tracks the focused entry;
* `FileInfo` (`TFileInfoPane`): the directory and wildcard being listed, and the name,
  size and date of the focused entry.

Reading directories is `HyperVision.FileDialog`'s job.
-/

namespace HyperVision

/-- A local date and time, to the minute. -/
structure FileTime where
  year : Nat
  /-- `1‥12`. -/
  month : Nat
  day : Nat
  hour : Nat
  minute : Nat
deriving DecidableEq, Repr, Inhabited

namespace FileTime

private def monthNames : Array String :=
  #["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

/-- `n` in decimal, padded on the left with `c` to `width` characters. -/
def pad (n width : Nat) (c : Char := ' ') : String :=
  let s := toString n
  String.ofList (List.replicate (width - s.length) c) ++ s

/-- Turbo Vision's format, `Sep 25, 2026  12:54pm`. -/
def format (t : FileTime) : String :=
  let h := t.hour % 12
  s!"{monthNames[t.month - 1]?.getD "???"} {pad t.day 2}, {pad t.year 4}  " ++
    s!"{pad (if h == 0 then 12 else h) 2}:{pad t.minute 2 '0'}{if t.hour < 12 then "am" else "pm"}"

end FileTime

/-- A directory entry. -/
structure FileEntry where
  name : String
  isDir : Bool := false
  /-- Size in bytes. -/
  size : Nat := 0
  modified : Option FileTime := none
deriving DecidableEq, Repr, Inhabited

namespace FileEntry

/-- The entry for the parent directory. -/
def parent : FileEntry := { name := "..", isDir := true }

/-- How the entry is listed: directories end in `/`. -/
def display (e : FileEntry) : String := if e.isDir then e.name ++ "/" else e.name

/-- Files come first, then directories, then `..`. -/
def rank (e : FileEntry) : Nat := if e.name == ".." then 2 else if e.isDir then 1 else 0

/-- `TFileCollection`'s order: by `rank`, then by name. -/
def le (a b : FileEntry) : Bool := a.rank < b.rank || (a.rank == b.rank && !decide (b.name < a.name))

def sort (es : Array FileEntry) : Array FileEntry := (es.toList.mergeSort le).toArray

end FileEntry

/-! ## Wildcards -/

/-- Whether `name` matches the pattern `pat`: `*` matches any run of characters and `?`
any single character. -/
def globMatch : List Char → List Char → Bool
  | [], s => s.isEmpty
  | '*' :: p, s =>
    globMatch p s || match s with
      | [] => false
      | _ :: s' => globMatch ('*' :: p) s'
  | '?' :: p, _ :: s => globMatch p s
  | c :: p, d :: s => c == d && globMatch p s
  | _ :: _, [] => false
termination_by p s => p.length + s.length

/-- Whether a name contains wildcard characters. -/
def isWild (s : String) : Bool := s.any fun c => c == '*' || c == '?'

/-- The patterns of a wildcard: `*.lean; *.md` has two. -/
def wildcardPatterns (wildcard : String) : List String :=
  (wildcard.splitOn ";").filterMap fun p =>
    let cs := (p.toList.dropWhile (· == ' ')).reverse.dropWhile (· == ' ') |>.reverse
    if cs.isEmpty then none else some (String.ofList cs)

/-- Whether `name` matches one of the patterns of `wildcard`. -/
def matchesWildcard (wildcard name : String) : Bool :=
  (wildcardPatterns wildcard).any fun p => globMatch p.toList name.toList

/-! ## The file list -/

/-- The directory `dir` and the wildcard, as one path (`/home/me/*.lean`). -/
def joinPath (dir name : String) : String :=
  if dir.endsWith "/" then dir ++ name else dir ++ "/" ++ name

/-- The name, size and date of the focused entry, and what is listed (`TFileInfoPane`). -/
structure FileInfo where
  /-- The directory and wildcard being listed. -/
  path : String := ""
  entry : Option FileEntry := none
deriving Inhabited, Repr

/--
Turbo Vision's `TFileList`: the entries of a directory, sorted, in two columns. The
bottom row is a scroll bar whose value is the focused entry. Focus changes are
reported with `Reply.changed`, so the window can show the focused entry in the
file name field (`field`) and in its `FileInfo` pane.
-/
structure FileList where
  /-- The directory listed (absolute). -/
  dir : String
  /-- Files are listed when they match this; directories always are. -/
  wildcard : String := "*"
  /-- Sorted by `FileEntry.le`. -/
  entries : Array FileEntry := #[]
  focused : Nat := 0
  /-- The entry in the top-left corner; always at the top of a column. -/
  top : Nat := 0
  /-- Name of the input line that shows the focused entry (`TFileInputLine`). -/
  field : String := ""
  /-- Type-ahead search: the prefix typed so far (`TSortedListBox`). -/
  search : String := ""
  /-- The file the dialog accepted, once it has. -/
  chosen : Option String := none
  /-- While the button is held after a press on the scroll bar: whether it grabbed the thumb. -/
  scrollGrab : Option Bool := none
deriving Inhabited, Repr

namespace FileList

def columns : Nat := 2

/-- Rows of entries: all but the bottom row, which holds the scroll bar. -/
def rows (s : Size) : Nat := max (s.h - 1) 1

/-- Entries visible at once. -/
def page (s : Size) : Nat := rows s * columns

/-- Width of a column, including the divider on its right (as `TListViewer` computes it). -/
def colWidth (s : Size) : Nat := s.w / columns + 1

/-- Focuses entry `i` (clamped to the list), scrolling by whole columns so that it is
visible (`TListViewer::focusItem`). -/
def focusItem (l : FileList) (s : Size) (i : Int) : FileList :=
  let f := (clampInt i 0 (l.entries.size - 1 : Nat)).toNat
  let r := rows s
  let top :=
    if f < l.top then f - f % r
    else if f ≥ l.top + page s then f - f % r - r * (columns - 1)
    else l.top
  { l with focused := f, top, search := "" }

/-- Scrolls so that the focused entry is shown at size `s` (after the list was resized). -/
def adjust (l : FileList) (s : Size) : FileList := { l.focusItem s l.focused with search := l.search }

/-- The entries of `dir` (already sorted) replace the list, focusing the first. -/
def load (l : FileList) (dir wildcard : String) (entries : Array FileEntry) : FileList :=
  { l with dir, wildcard, entries, focused := 0, top := 0, search := "", chosen := none }

def focusedEntry? (l : FileList) : Option FileEntry := l.entries[l.focused]?

/-- What the file name field shows for the focused entry: its name, and for a directory
also `/` and the wildcard, so that accepting it opens the directory. -/
def fieldText (l : FileList) : String :=
  match l.focusedEntry? with
  | some e => if e.isDir then e.name ++ "/" ++ l.wildcard else e.name
  | none => l.wildcard

def info (l : FileList) : FileInfo := { path := joinPath l.dir l.wildcard, entry := l.focusedEntry? }

/-- The first entry whose name starts with `pre`, ignoring case. -/
def findPrefix (l : FileList) (pre : String) : Option Nat :=
  let pre := pre.toList.map Char.toLower
  l.entries.findIdx? fun e => pre.isPrefixOf (e.name.toList.map Char.toLower)

/-- Type-ahead: extends the search prefix by `c` if some entry starts with it. -/
def typeAhead (l : FileList) (s : Size) (c : Char) : FileList × Reply :=
  let pre := l.search.push c
  match l.findPrefix pre with
  | some i => ({ l.focusItem s i with search := pre }, .changed)
  | none => (l, .handled)

/-- `Backspace` during type-ahead: shortens the prefix and goes back to its first match. -/
def searchBack (l : FileList) (s : Size) : FileList × Reply :=
  if l.search.isEmpty then (l, .ignored) else
  let pre := String.ofList l.search.toList.dropLast
  match (if pre.isEmpty then none else l.findPrefix pre) with
  | some i => ({ l.focusItem s i with search := pre }, .changed)
  | none => ({ l with search := pre }, .handled)

def handleKey (l : FileList) (s : Size) (k : KeyEvent) : FileList × Reply :=
  let l := l.adjust s
  let f : Int := l.focused
  let r : Int := rows s
  let go (i : Int) : FileList × Reply := (l.focusItem s i, .changed)
  if k.mods.alt then (l, .ignored) else
  match k.key with
  | .up => go (f - 1)
  | .down => go (f + 1)
  | .left => go (f - r)
  | .right => go (f + r)
  | .pageUp => go (if k.mods.ctrl then 0 else f - page s)
  | .pageDown => go (if k.mods.ctrl then l.entries.size - 1 else f + page s)
  | .home => go (if k.mods.ctrl then 0 else l.top)
  | .end => go (if k.mods.ctrl then l.entries.size - 1 else l.top + page s - 1)
  | .backspace => l.searchBack s
  | .char ' ' => if k.mods.isNone && l.focused < l.entries.size then (l, .activated) else (l, .ignored)
  | _ =>
    match k.text? with
    | some c => l.typeAhead s c
    | none => (l, .ignored)

/-- The scroll bar along the bottom row; its value is the focused entry. -/
def scrollBar (l : FileList) (s : Size) : ScrollBar :=
  { vertical := false, length := s.w, value := l.focused, max := l.entries.size - 1 }

/-- The entry shown at `p` (clamped to the last entry), for a point in the list area. -/
def itemAt (l : FileList) (s : Size) (p : Point) : Int :=
  l.top + (p.x / colWidth s) * rows s + p.y

def handleMouse (l : FileList) (s : Size) (m : MouseEvent) : FileList × Reply :=
  let l := l.adjust s
  let r : Int := rows s
  let f : Int := l.focused
  let p := m.pos
  let inList := 0 ≤ p.x && p.x < s.w && 0 ≤ p.y && p.y < r
  match m.action with
  | .wheelUp => (l.focusItem s (f - r), .changed)
  | .wheelDown => (l.focusItem s (f + r), .changed)
  | .press =>
    if p.y == ((s.h - 1 : Nat) : Int) && s.h ≥ 2 then
      -- The scroll bar: arrows step a column, the page areas a page, the thumb is grabbed.
      let sb := l.scrollBar s
      let off := p.x.toNat
      match sb.hit off with
      | .thumb => ({ l with scrollGrab := some true }, .handled)
      | part =>
        let delta : Int := match part with
          | .decArrow => -r | .incArrow => r | .pageDec => -(page s : Int) | _ => page s
        ({ l.focusItem s (f + delta) with scrollGrab := some false }, .changed)
    else if inList then
      let i := l.itemAt s p
      if m.double && i < l.entries.size then (l.focusItem s i, .activated) else (l.focusItem s i, .changed)
    else (l, .handled)
  | .drag =>
    match l.scrollGrab with
    | some true => (l.focusItem s ((l.scrollBar s).valueAt p.x.toNat), .changed)
    | some false => (l, .handled)
    | none =>
      -- Dragging outside the list scrolls it a column at a time (`TListViewer`).
      if inList then (l.focusItem s (l.itemAt s p), .changed)
      else if m.pos.x < 0 then (l.focusItem s (f - r), .changed)
      else if m.pos.x ≥ s.w then (l.focusItem s (f + r), .changed)
      else if m.pos.y < 0 then (l.focusItem s (f - f % r), .changed)
      else (l.focusItem s (f - f % r + r - 1), .changed)
  | .release => ({ l with scrollGrab := none }, .handled)
  | .move => (l, .ignored)

def draw (l : FileList) (ctx : DrawCtx) : DrawM Unit := do
  let c := ctx.theme.dialog
  let s := ctx.size
  let l := l.adjust s
  let r := rows s
  let cw := colWidth s
  for y in [0:s.h - 1] do
    for j in [0:columns] do
      let item := l.top + j * r + y
      let x0 := j * cw
      let width := if j + 1 == columns then s.w - x0 + 1 else cw
      let attr :=
        if item == l.focused && item < l.entries.size then
          if ctx.focused then c.listFocused else c.listSelected
        else c.listNormal
      Draw.hline x0 y width ' ' attr
      match l.entries[item]? with
      | some e => Draw.putStr (x0 + 1) y (String.ofList (e.display.toList.take (width - 2))) attr
      | none => if item == 0 then Draw.putStr (x0 + 1) y "<empty>" c.listNormal
      Draw.putChar (x0 + width - 1) y '│' c.listDivider
  if s.h ≥ 2 then (l.scrollBar s).draw 0 (s.h - 1 : Nat) c.scrollPage c.scrollControls

end FileList

instance : Widget FileList where
  draw := FileList.draw
  handleKey := FileList.handleKey
  handleMouse := FileList.handleMouse
  wantsText _ := true
  cancelMouse l := { l with scrollGrab := none }

namespace FileInfo

/-- The last `n` characters of `s`, with `…` in front if it had to be cut. -/
def tail (s : String) (n : Nat) : String :=
  let cs := s.toList
  if cs.length ≤ n then s else if n == 0 then "" else String.ofList ('…' :: cs.drop (cs.length - (n - 1)))

/-- The size column: the size in bytes, or `Directory`. -/
def sizeText (e : FileEntry) : String := if e.isDir then "Directory" else toString e.size

def draw (i : FileInfo) (ctx : DrawCtx) : DrawM Unit := do
  let attr := ctx.theme.dialog.infoPane
  let w := ctx.size.w
  Draw.fill ⟨0, 0, w, ctx.size.h⟩ ' ' attr
  Draw.putStr 1 0 (tail i.path (w - 2)) attr
  if let some e := i.entry then
    -- The date on the right, the size right-aligned before it, the name in what is left.
    let dateX := w - 22
    let size := sizeText e
    let sizeX := dateX - 2 - size.length
    Draw.putStr 1 1 (String.ofList (e.name.toList.take (sizeX - 2))) attr
    Draw.putStr sizeX 1 size attr
    if let some t := e.modified then Draw.putStr dateX 1 t.format attr

end FileInfo

instance : Widget FileInfo where
  draw := FileInfo.draw
  focusable _ := false

end HyperVision
