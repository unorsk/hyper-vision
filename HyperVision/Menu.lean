import HyperVision.Widget

/-!
# Menus and the status line

The top menu bar with drop-down boxes and nested sub-menus (`TMenuBar`,
`TMenuBox`) and the bottom status line (`TStatusLine`). This module holds the
data, geometry and drawing; keyboard and mouse tracking live in `App`.
-/

namespace HyperVision

inductive MenuItem (α : Type) where
  | command (text : HotText) (cmd : Command α) (key : Option KeyEvent) (enabled : Bool)
  | submenu (text : HotText) (items : Array (MenuItem α))
  | separator
deriving Inhabited

/-- A top-level entry of the menu bar. -/
structure Menu (α : Type) where
  title : HotText
  items : Array (MenuItem α)
deriving Inhabited

namespace MenuItem

variable {α : Type}

/-- A command item; `key` is a global shortcut, shown right-aligned. -/
def item (text : String) (cmd : Command α) (key : Option KeyEvent := none) (enabled : Bool := true) :
    MenuItem α :=
  .command (HotText.parse text) cmd key enabled

def sub (text : String) (items : Array (MenuItem α)) : MenuItem α :=
  .submenu (HotText.parse text) items

def text? : MenuItem α → Option HotText
  | .command t .. => some t
  | .submenu t _ => some t
  | .separator => none

def isSeparator : MenuItem α → Bool
  | .separator => true
  | _ => false

def enabled : MenuItem α → Bool
  | .command _ _ _ e => e
  | .submenu .. => true
  | .separator => false

def hotkey? (i : MenuItem α) : Option Char := i.text? >>= (·.hotkey?)

end MenuItem

def Menu.new {α : Type} (title : String) (items : Array (MenuItem α)) : Menu α :=
  ⟨HotText.parse title, items⟩

/-- A status line entry: shows `text` (if non-empty) and binds `key` to `cmd`. -/
structure StatusItem (α : Type) where
  text : HotText
  key : KeyEvent
  cmd : Command α
deriving Inhabited

def StatusItem.new {α : Type} (text : String) (key : KeyEvent) (cmd : Command α) : StatusItem α :=
  ⟨HotText.parse text, key, cmd⟩

/-- Which menu entries are highlighted: the bar entry and, for each open box, its item. -/
structure MenuTrack where
  bar : Nat
  /-- Highlighted item of every open drop-down box, outermost first (empty: none open). -/
  path : Array Nat
deriving BEq, Repr, Inhabited

namespace MenuBar

variable {α : Type}

/-- Column of bar entry `i` (entries start at column 1, each padded by a blank on both sides). -/
def itemX (menus : Array (Menu α)) (i : Nat) : Nat :=
  1 + ((menus.extract 0 i).foldl (fun acc m => acc + m.title.width + 2) 0)

def itemAt? (menus : Array (Menu α)) (x : Int) : Option Nat :=
  (List.range menus.size).find? fun i =>
    let x0 : Int := itemX menus i
    x0 ≤ x && x < x0 + ((menus[i]?.map (·.title.width)).getD 0) + 2

/-- Width of a drop-down box, as computed by `TMenuBox::getRect`. -/
def boxWidth (items : Array (MenuItem α)) : Nat :=
  items.foldl (init := 10) fun acc it => match it with
    | .command t _ k _ => max acc (t.width + 6 + ((k.map (·.label.length + 2)).getD 0))
    | .submenu t _ => max acc (t.width + 9)
    | .separator => acc

/-- Moves `r` left/up so it fits inside `screen`. -/
def fit (r : Rect) (screen : Size) : Rect :=
  { r with x := max 0 (min r.x ((screen.w : Int) - r.w)), y := max 1 (min r.y ((screen.h : Int) - 1 - r.h)) }

/-- The open drop-down boxes (outermost first) with their items. -/
def boxes (menus : Array (Menu α)) (t : MenuTrack) (screen : Size) :
    Array (Rect × Array (MenuItem α)) := Id.run do
  let some m := menus[t.bar]? | return #[]
  if t.path.isEmpty then return #[]
  let mut items := m.items
  let mut r := fit ⟨(itemX menus t.bar : Int) - 1, 1, boxWidth items, items.size + 2⟩ screen
  let mut out := #[(r, items)]
  for k in [0:t.path.size - 1] do
    let sel := t.path[k]?.getD 0
    match items[sel]? with
    | some (.submenu _ sub) =>
      items := sub
      r := fit ⟨r.x + 2, r.y + sel + 2, boxWidth sub, sub.size + 2⟩ screen
      out := out.push (r, items)
    | _ => break
  return out

def drawBar (menus : Array (Menu α)) (track : Option MenuTrack) (c : MenuColors) (width : Nat) :
    DrawM Unit := do
  Draw.hline 0 0 width ' ' c.normal
  for h : i in [0:menus.size] do
    let m := menus[i]
    let x := itemX menus i
    if x + m.title.width < width then
      let sel := (track.map (·.bar)) == some i
      let (normal, hot) := if sel then (c.selected, c.selectedShortcut) else (c.normal, c.shortcut)
      Draw.putChar x 0 ' ' normal
      Draw.putHot (x + 1) 0 m.title normal hot
      Draw.putChar (x + 1 + m.title.width) 0 ' ' normal

def drawBox (r : Rect) (items : Array (MenuItem α)) (highlight : Option Nat) (t : Theme) :
    DrawM Unit := do
  let c := t.menu
  let w := r.w
  Draw.shadow r t.shadow t.shadowOnBlack
  Draw.within r do
    let frameRow (y : Nat) (l m rt : Char) : DrawM Unit := do
      Draw.hline 0 y w ' ' c.normal
      Draw.putChar 1 y l c.normal
      Draw.hline 2 y (w - 4) m c.normal
      Draw.putChar (w - 2) y rt c.normal
    frameRow 0 '┌' '─' '┐'
    for h : i in [0:items.size] do
      let y := i + 1
      match items[i] with
      | .separator => frameRow y '├' '─' '┤'
      | it =>
        frameRow y '│' ' ' '│'
        let sel := highlight == some i
        let (normal, hot) :=
          if !it.enabled then (if sel then (c.selectedDisabled, c.selectedDisabled) else (c.disabled, c.disabled))
          else if sel then (c.selected, c.selectedShortcut) else (c.normal, c.shortcut)
        Draw.hline 2 y (w - 4) ' ' normal
        Draw.putHot 3 y (it.text?.getD default) normal hot
        match it with
        | .submenu .. => Draw.putChar (w - 4) y '►' normal
        | .command _ _ (some k) _ =>
          let label := k.label
          Draw.putStr (w - 3 - label.length) y label normal
        | _ => pure ()
    frameRow (items.size + 1) '└' '─' '┘'

/-- First item that can be highlighted. -/
def firstItem (items : Array (MenuItem α)) : Nat :=
  (items.findIdx? (!·.isSeparator)).getD 0

/-- Next highlightable item in direction `forward`, wrapping around. -/
def step (items : Array (MenuItem α)) (i : Nat) (forward : Bool) : Nat :=
  let n := items.size
  if n == 0 then 0 else
  let cands := (List.range n).map fun k => if forward then (i + 1 + k) % n else (i + n - 1 - k) % n
  (cands.find? fun j => !((items[j]?.map (·.isSeparator)).getD true)).getD i

/-- Every command reachable from an item, with its shortcut and enabled state. -/
def itemShortcuts : MenuItem α → Array (KeyEvent × Command α × Bool)
  | .command _ cmd (some k) enabled => #[(k, cmd, enabled)]
  | .submenu _ sub => sub.attach.flatMap fun ⟨it, _⟩ => itemShortcuts it
  | _ => #[]

def shortcuts (items : Array (MenuItem α)) : Array (KeyEvent × Command α × Bool) :=
  items.flatMap itemShortcuts

end MenuBar

namespace StatusLine

variable {α : Type}

/-- Column ranges of the visible items: `(item index, x, width)`. -/
def layout (items : Array (StatusItem α)) : Array (Nat × Nat × Nat) := Id.run do
  let mut x := 0
  let mut out := #[]
  for h : i in [0:items.size] do
    let l := items[i].text.width
    if l > 0 then
      out := out.push (i, x, l + 2)
      x := x + l + 2
  return out

def itemAt? (items : Array (StatusItem α)) (x : Int) : Option Nat :=
  (layout items).findSome? fun (i, x0, w) => if (x0 : Int) ≤ x && x < x0 + w then some i else none

def draw (items : Array (StatusItem α)) (hint : String) (pressed : Option Nat) (c : MenuColors)
    (y : Int) (width : Nat) : DrawM Unit := do
  Draw.hline 0 y width ' ' c.normal
  let mut endX := 0
  for (i, x, w) in layout items do
    if x + w ≤ width then
      let (normal, hot) := if pressed == some i then (c.selected, c.selectedShortcut)
        else (c.normal, c.shortcut)
      Draw.hline x y w ' ' normal
      Draw.putHot (x + 1) y ((items[i]?.map (·.text)).getD default) normal hot
      endX := x + w
  if !hint.isEmpty && endX + 2 < width then
    Draw.putStr endX y ("│ " ++ hint) c.normal

end StatusLine

end HyperVision
