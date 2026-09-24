import HyperVision.Desktop
import HyperVision.Menu
import HyperVision.Input
import HyperVision.Terminal

/-!
# Application

`App.run` owns the terminal and the event loop. It routes keyboard and mouse
events through the menu bar, drop-down lists, the status line and the desktop,
tracks mouse capture for dragging/resizing windows, and repaints the screen
through the differential renderer.
-/

namespace HyperVision

/-- An open drop-down list attached to a combo box (Turbo Vision's history window). -/
structure Popup where
  /-- Screen coordinates, frame included. -/
  rect : Rect
  items : Array String
  current : Nat
  top : Nat := 0
  window : Nat
  control : Nat
deriving Inhabited

namespace Popup

def listHeight (p : Popup) : Nat := p.rect.h - 2

/-- Scrolls so the highlighted item is visible. -/
def adjust (p : Popup) : Popup :=
  let h := max p.listHeight 1
  let current := min p.current (p.items.size - 1)
  let top := if current < p.top then current else if current ≥ p.top + h then current + 1 - h else p.top
  { p with current, top }

def moveBy (p : Popup) (delta : Int) : Popup :=
  { p with current := (clampInt (p.current + delta) 0 (p.items.size - 1)).toNat }.adjust

def itemAt? (p : Popup) (pos : Point) : Option Nat :=
  let row := pos.y - p.rect.y - 1
  let i := (p.top : Int) + row
  if p.rect.x < pos.x && pos.x < p.rect.right - 1 && 0 ≤ row && row < p.listHeight && i < p.items.size
  then some i.toNat else none

def draw (p : Popup) (t : Theme) : DrawM Unit := do
  let c := t.popup
  let w := p.rect.w
  let h := p.rect.h
  Draw.shadow p.rect t.shadow t.shadowOnBlack
  Draw.within p.rect do
    Draw.fill ⟨0, 0, w, h⟩ ' ' c.frame
    Draw.box ⟨0, 0, w, h⟩ BoxChars.double c.frame
    Draw.putStr 2 0 "[ ]" c.frame
    Draw.putChar 3 0 '■' c.icon
    for row in [0:p.listHeight] do
      let i := p.top + row
      if let some s := p.items[i]? then
        let attr := if i == p.current then c.focused else c.item
        Draw.hline 1 (row + 1) (w - 2) ' ' attr
        Draw.putStr 2 (row + 1) (fitString s (w - 4)) attr
    if p.items.size > p.listHeight then
      let sb : ScrollBar :=
        { vertical := true, length := p.listHeight, value := p.current, max := p.items.size - 1 }
      sb.draw (w - 1 : Nat) 1 c.scrollPage c.scrollControls

end Popup

/-- Who receives mouse events between a press and the matching release. -/
inductive Capture where
  | none
  | move (win : Nat) (grab : Point)
  | resize (win : Nat) (grab : Point)
  | control (win : Nat) (idx : Nat)
  | closeIcon (win : Nat)
  | scroll (win : Nat) (vertical : Bool) (thumb : Bool)
  | status (idx : Nat)
  | menu
deriving BEq, Inhabited

/-- A Turbo Vision application: menus, status line, theme and a command handler. -/
structure App (α : Type) where
  menuBar : Array (Menu α)
  statusLine : Array (StatusItem α)
  /-- Text shown after the status line items. -/
  statusHint : String := ""
  theme : Theme := Theme.turboVision
  /-- Handles application commands. The window whose control issued the command
  (or the active window) is passed along so its values can be read. -/
  onCommand : α → Option (Window α) → Desktop α → IO (Desktop α) := fun _ _ d => pure d
  /-- Draw a DOS-style block mouse cursor (handy for screen recordings). -/
  mouseCursor : Bool := false

/-- The mutable part of a running application. -/
structure AppState (α : Type) where
  desktop : Desktop α
  screen : Size
  menu : Option MenuTrack := none
  popup : Option Popup := none
  capture : Capture := .none
  statusPressed : Option Nat := none
  mouse : Option Point := none
  lastClick : Option (Nat × Point) := none
  /-- Keyboard move/resize in progress: the window and its original bounds. -/
  keyDrag : Option (Nat × Rect) := none
  quit : Bool := false
deriving Inhabited

abbrev AppM (α : Type) := ReaderT (App α) (StateT (AppState α) IO)

namespace App

variable {α : Type}

def desktopRect (s : Size) : Rect := ⟨0, 1, s.w, s.h - 2⟩

private def modifyDesktop (f : Desktop α → Desktop α) : AppM α Unit :=
  modify fun s => { s with desktop := f s.desktop }

/-! ### Commands -/

def dispatch (cmd : Command α) (source : Option Nat := none) : AppM α Unit := do
  let app ← read
  let d := (← get).desktop
  let target := source <|> d.top?.map (·.id)
  match cmd with
  | .quit => modify fun s => { s with quit := true }
  | .close =>
    if let some id := target then
      if (d.find? id).any (·.flags.close) then modifyDesktop (·.close id)
  | .ok | .cancel => if let some id := target then modifyDesktop (·.close id)
  | .zoom => if let some id := target then modifyDesktop (·.toggleZoom id)
  | .resize =>
    if let some w := d.top? then
      if w.flags.move || w.flags.grow then
        modify fun s => { s with keyDrag := some (w.id, w.bounds) }
        modifyDesktop (·.modify w.id fun w => { w with dragging := true })
  | .nextWindow => modifyDesktop Desktop.next
  | .prevWindow => modifyDesktop Desktop.prev
  | .tile => modifyDesktop Desktop.tile
  | .cascade => modifyDesktop Desktop.cascade
  | .menu => modify fun s => { s with menu := some ⟨0, #[]⟩ }
  | .user a =>
    let d' ← app.onCommand a (target.bind d.find?) d
    modify fun s => { s with desktop := d' }

/-- Handles what a window reported back. -/
def windowReply (id : Nat) : WindowReply α → AppM α Unit
  | .ignored | .handled => pure ()
  | .command c => dispatch c (some id)
  | .dropDown ctrl anchor items current => do
    let st ← get
    let some w := st.desktop.find? id | return
    if items.isEmpty then return
    let a := anchor.translate w.bounds.origin
    let desk := desktopRect st.screen
    let h := min items.size 6 + 2
    let y := if a.y - 1 + h > desk.bottom then desk.bottom - h else a.y - 1
    let rect : Rect := ⟨a.x - 1, max desk.y y, a.w + 2, h⟩
    modify fun s => { s with popup := some { rect, items, current, window := id, control := ctrl : Popup }.adjust
                             capture := .none }

/-- Runs a window's handler on the window with id `id` and processes its reply. -/
def withWindow (id : Nat) (f : Window α → Window α × WindowReply α) : AppM α Unit := do
  let some w := (← get).desktop.find? id | return
  let (w', r) := f w
  modifyDesktop fun d => d.modify id fun _ => w'
  windowReply id r

/-! ### Menus -/

def openMenu (bar : Nat) (dropDown : Bool) : AppM α Unit := do
  let app ← read
  let path := if dropDown then #[MenuBar.firstItem ((app.menuBar[bar]?.map (·.items)).getD #[])] else #[]
  modify fun s => { s with menu := some ⟨bar, path⟩, capture := .none }

private def setTrack (t : Option MenuTrack) : AppM α Unit := modify fun s => { s with menu := t }

/-- Executes (or opens) item `i` of the innermost box. -/
def activateItem (t : MenuTrack) (items : Array (MenuItem α)) (i : Nat) : AppM α Unit :=
  match items[i]? with
  | some (.submenu _ sub) => setTrack (some { t with path := t.path.push (MenuBar.firstItem sub) })
  | some (.command _ cmd _ true) => do
    setTrack none
    dispatch cmd
  | _ => pure ()

def menuKey (t : MenuTrack) (k : KeyEvent) : AppM α Unit := do
  let app ← read
  let st ← get
  let n := app.menuBar.size
  if n == 0 then setTrack none; return
  let boxes := MenuBar.boxes app.menuBar t st.screen
  let depth := t.path.size
  let inner := (boxes.back?.map (·.2)).getD #[]
  let cur := t.path.back?.getD 0
  let setCur (i : Nat) : AppM α Unit :=
    setTrack (some { t with path := t.path.pop.push i })
  let barHot (c : Char) : Option Nat := app.menuBar.findIdx? (·.title.hotkey? == some c.toLower)
  match k.key with
  | .escape => setTrack (if depth == 0 then none else some { t with path := t.path.pop })
  | .f 10 => setTrack none
  | .left =>
    if depth ≤ 1 then openMenu ((t.bar + n - 1) % n) (depth == 1)
    else setTrack (some { t with path := t.path.pop })
  | .right =>
    match inner[cur]? with
    | some (.submenu _ sub) =>
      if depth ≥ 1 then setTrack (some { t with path := t.path.push (MenuBar.firstItem sub) })
      else openMenu ((t.bar + 1) % n) false
    | _ => openMenu ((t.bar + 1) % n) (depth ≥ 1)
  | .down => if depth == 0 then openMenu t.bar true else setCur (MenuBar.step inner cur true)
  | .up => if depth == 0 then openMenu t.bar true else setCur (MenuBar.step inner cur false)
  | .home => if depth > 0 then setCur (MenuBar.firstItem inner)
  | .end => if depth > 0 then setCur (MenuBar.step inner 0 false)
  | .enter => if depth == 0 then openMenu t.bar true else activateItem t inner cur
  | .char c =>
    if k.mods.alt || depth == 0 then
      if let some i := barHot c then openMenu i true
    else
      if let some i := inner.findIdx? (·.hotkey? == some c.toLower) then
        let t := { t with path := t.path.pop.push i }
        setTrack (some t)
        activateItem t inner i
  | _ => pure ()

def menuMouse (t : MenuTrack) (m : MouseEvent) : AppM α Unit := do
  let app ← read
  let st ← get
  let boxes := MenuBar.boxes app.menuBar t st.screen
  let hit := (List.range boxes.size).reverse.find? fun k =>
    (boxes[k]?.map (·.1.contains m.pos)).getD false
  match hit, boxes[hit.getD 0]? with
  | some k, some (r, items) =>
    let row := m.pos.y - r.y - 1
    if 0 ≤ row && row < items.size && r.x + 2 ≤ m.pos.x && m.pos.x < r.right - 2 then
      let i := row.toNat
      if (items[i]?.map (·.isSeparator)).getD true then return
      let t := { t with path := (t.path.extract 0 k).push i }
      setTrack (some t)
      if m.action == .release then activateItem t items i
  | _, _ =>
    if m.pos.y == 0 then
      match MenuBar.itemAt? app.menuBar m.pos.x with
      | some i =>
        if m.action == .press && i == t.bar && !t.path.isEmpty then setTrack none
        else if (m.action == .press || m.action == .drag) && (i != t.bar || t.path.isEmpty) then
          openMenu i true
      | none => if m.action == .press then setTrack none
    else if m.action == .press then setTrack none

/-! ### Drop-down lists -/

def choosePopup (p : Popup) : AppM α Unit := do
  modify fun s => { s with popup := none }
  modifyDesktop fun d => d.modify p.window fun w =>
    { w with controls := w.controls.modify p.control fun c => match c.kind with
      | .comboBox cb => { c with kind := .comboBox (cb.choose p.current) }
      | _ => c }

/-- Handles navigation keys in an open drop-down list; returns `false` for other keys. -/
def popupKey (p : Popup) (k : KeyEvent) : AppM α Bool := do
  let set (p : Popup) : AppM α Bool := do
    modify fun s => { s with popup := some p }
    return true
  match k.key with
  | .up => set (p.moveBy (-1))
  | .down => set (p.moveBy 1)
  | .pageUp => set (p.moveBy (-(p.listHeight : Int)))
  | .pageDown => set (p.moveBy p.listHeight)
  | .home => set (p.moveBy (-(p.items.size : Int)))
  | .end => set (p.moveBy p.items.size)
  | .enter => choosePopup p; return true
  | .escape => modify (fun s => { s with popup := none }); return true
  | _ => return false

def popupMouse (p : Popup) (m : MouseEvent) : AppM α Unit := do
  let set (p : Popup) : AppM α Unit := modify fun s => { s with popup := some p }
  match m.action with
  | .wheelUp => set { p with top := p.top - 1 }
  | .wheelDown => set { p with top := min (p.top + 1) (p.items.size - p.listHeight) }
  | .press | .drag | .release =>
    if !p.rect.contains m.pos then
      if m.action == .press then modify fun s => { s with popup := none }
    else if m.pos.y == p.rect.y && m.pos.x - p.rect.x ≥ 2 && m.pos.x - p.rect.x ≤ 4 then
      if m.action == .release then modify fun s => { s with popup := none }
    else match p.itemAt? m.pos with
      | some i =>
        let p := { p with current := i }
        if m.action == .release then choosePopup p else set p
      | none =>
        -- Scroll bar on the right edge.
        if m.pos.x == p.rect.right - 1 && m.action == .press then
          let sb : ScrollBar := { vertical := true, length := p.listHeight, value := p.top
                                  max := p.items.size - p.listHeight }
          let off := (m.pos.y - p.rect.y - 1).toNat
          let top : Int := match sb.hit off with
            | .decArrow => p.top - 1 | .incArrow => p.top + 1
            | .pageDec => (p.top : Int) - p.listHeight | .pageInc => p.top + p.listHeight
            | .thumb => sb.valueAt off
          set { p with top := (clampInt top 0 sb.max).toNat }
  | _ => pure ()

/-! ### Keyboard -/

/-- Keyboard move/resize (`Ctrl-F5`): arrows move, `Shift`+arrows resize, `Ctrl` moves
further, `Enter` accepts and `Esc` restores the original bounds. -/
def keyDragKey (id : Nat) (orig : Rect) (k : KeyEvent) : AppM α Unit := do
  let some w := (← get).desktop.find? id | modify fun s => { s with keyDrag := none }
  let finish : AppM α Unit := do
    modify fun s => { s with keyDrag := none }
    modifyDesktop (·.modify id fun w => { w with dragging := false })
  let step : Int := if k.mods.ctrl then 8 else 1
  let delta : Option Point := match k.key with
    | .left => some ⟨-step, 0⟩ | .right => some ⟨step, 0⟩
    | .up => some ⟨0, -(if k.mods.ctrl then 4 else 1)⟩
    | .down => some ⟨0, if k.mods.ctrl then 4 else 1⟩
    | _ => none
  match k.key, delta with
  | .enter, _ => finish
  | .escape, _ =>
    modifyDesktop (·.modify id fun w => w.setBounds orig)
    finish
  | _, some dp =>
    if k.mods.shift then
      if w.flags.grow then
        let s := (⟨w.bounds.w, w.bounds.h⟩ : Point) + dp
        modifyDesktop (·.resizeTo id ⟨s.x.toNat, s.y.toNat⟩)
    else if w.flags.move then modifyDesktop (·.moveTo id (w.bounds.origin + dp))
  | _, _ => pure ()

def handleKey (k : KeyEvent) : AppM α Unit := do
  let app ← read
  let st ← get
  if let some (id, orig) := st.keyDrag then return (← keyDragKey id orig k)
  -- As in Turbo Vision, the status line sees every key first, so its bindings
  -- (Alt-X, F5, …) work even while a menu or a drop-down list is open.
  let statusCmd := app.statusLine.find? (·.key == k) |>.map (·.cmd)
  let isMenuCmd := statusCmd.any fun | .menu => true | _ => false
  if let some cmd := statusCmd then
    if !(st.menu.isSome && isMenuCmd) then
      modify fun s => { s with menu := none, popup := none }
      return (← dispatch cmd)
  if let some t := st.menu then return (← menuKey t k)
  if let some p := st.popup then
    if ← popupKey p k then return
    modify fun s => { s with popup := none }
  let st ← get
  let modal := st.desktop.modalActive
  let barHot : Option Nat := match k.key with
    | .char c => if k.mods.alt && !modal then app.menuBar.findIdx? (·.title.hotkey? == some c.toLower) else none
    | _ => none
  let menuCmd := if modal then none else
    (app.menuBar.flatMap (MenuBar.shortcuts ·.items)).findSome? fun (key, cmd, enabled) =>
      if key == k && enabled then some cmd else none
  let windowNum : Option Nat := match k.key with
    | .char c => if k.mods.alt && '1' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat) else none
    | _ => none
  if let some i := barHot then openMenu i true
  else if k == KeyEvent.plain (.f 10) && !modal then openMenu 0 false
  else if let some cmd := menuCmd then dispatch cmd
  else if let some n := windowNum then modifyDesktop (·.selectNumber n)
  else if let some w := st.desktop.top? then withWindow w.id (·.handleKey k)

/-! ### Mouse -/

private def setDragging (id : Nat) (b : Bool) : AppM α Unit :=
  modifyDesktop (·.modify id fun w => { w with dragging := b })

/-- Continues a captured mouse interaction (drag or release). -/
def captured (c : Capture) (m : MouseEvent) : AppM α Unit := do
  let st ← get
  let release := m.action == .release
  match c with
  | .none | .menu => pure ()
  | .move id grab =>
    modifyDesktop (·.moveTo id (m.pos - grab))
    if release then setDragging id false
  | .resize id grab =>
    if let some w := st.desktop.find? id then
      let s := m.pos - w.bounds.origin + grab
      modifyDesktop (·.resizeTo id ⟨s.x.toNat, s.y.toNat⟩)
    if release then setDragging id false
  | .control id i =>
    if let some w := st.desktop.find? id then
      withWindow id (·.mouseControl i (m.relativeTo w.bounds.origin))
  | .closeIcon id =>
    if release then
      if let some w := st.desktop.find? id then
        let p := m.pos - w.bounds.origin
        if p.y == 0 && 2 ≤ p.x && p.x ≤ 4 then dispatch .close (some id)
  | .scroll id vertical thumb =>
    if thumb && m.action == .drag then
      if let some w := st.desktop.find? id then
        let p := m.pos - w.bounds.origin
        let off := if vertical then p.y - 1 else p.x - 18
        let len := ((if vertical then w.vScrollBar? else w.hScrollBar?).map (·.length)).getD 3
        let off := (clampInt off 1 (len - 2)).toNat
        modifyDesktop (·.modify id (·.scrollEditor vertical off))
  | .status i =>
    let over := m.pos.y == st.screen.h - 1 && StatusLine.itemAt? (← read).statusLine m.pos.x == some i
    modify fun s => { s with statusPressed := if over then some i else none }
    if release then
      modify fun s => { s with statusPressed := none }
      if over then
        if let some item := (← read).statusLine[i]? then dispatch item.cmd
  if release then modify fun s => { s with capture := .none }

/-- A left-button press on the desktop area. -/
def pressDesktop (m : MouseEvent) : AppM α Unit := do
  let d := (← get).desktop
  let some idx := (List.range d.windows.size).reverse.find? fun i =>
    (d.windows[i]?.map (·.bounds.contains m.pos)).getD false | return
  let some w := d.windows[idx]? | return
  let wasActive := idx + 1 == d.windows.size
  if d.modalActive && !wasActive then return
  modifyDesktop (·.raise w.id)
  let rel := m.pos - w.bounds.origin
  let capture (c : Capture) : AppM α Unit := modify fun s => { s with capture := c }
  match w.frameHit rel with
  | .close => if wasActive then capture (.closeIcon w.id)
  | .zoom => if wasActive then dispatch .zoom (some w.id)
  | .move =>
    if m.double && w.flags.zoom then dispatch .zoom (some w.id)
    else
      setDragging w.id true
      capture (.move w.id rel)
  | .resize =>
    setDragging w.id true
    capture (.resize w.id (⟨w.bounds.w, w.bounds.h⟩ - rel))
  | .vScroll off =>
    let thumb := (w.vScrollBar?.map (·.hit off == .thumb)).getD false
    modifyDesktop (·.modify w.id (·.scrollEditor true off))
    capture (.scroll w.id true thumb)
  | .hScroll off =>
    let thumb := (w.hScrollBar?.map (·.hit off == .thumb)).getD false
    modifyDesktop (·.modify w.id (·.scrollEditor false off))
    capture (.scroll w.id false thumb)
  | .interior =>
    if let some i := w.controlAt? rel then
      capture (.control w.id i)
      withWindow w.id (·.mouseControl i (m.relativeTo w.bounds.origin))
  | .border => pure ()

def handleMouse (m : MouseEvent) : AppM α Unit := do
  let app ← read
  -- Double-click detection.
  let now ← IO.monoMsNow
  let st ← get
  let m ← if m.action == .press then
      let double := st.lastClick.any fun (t, p) => p == m.pos && now - t < 400
      modify fun s => { s with lastClick := if double then none else some (now, m.pos) }
      pure { m with double }
    else pure m
  modify fun s => { s with mouse := some m.pos }
  let st ← get
  if let some t := st.menu then return (← menuMouse t m)
  if let some p := st.popup then return (← popupMouse p m)
  if st.capture != .none then
    if m.action != .press then return (← captured st.capture m)
    -- A press while captured means the release was lost: drop the stale capture.
    modify fun s => { s with capture := .none }
  let modal := st.desktop.modalActive
  match m.action with
  | .press =>
    if m.button != .left then return
    if m.pos.y == 0 then
      if !modal then
        if let some i := MenuBar.itemAt? app.menuBar m.pos.x then openMenu i true
    else if m.pos.y == st.screen.h - 1 then
      if let some i := StatusLine.itemAt? app.statusLine m.pos.x then
        modify fun s => { s with capture := .status i, statusPressed := some i }
    else pressDesktop m
  | .wheelUp | .wheelDown =>
    let d := st.desktop
    let some w := d.windows.reverse.find? (·.bounds.contains m.pos) | return
    if modal && d.top?.map (·.id) != some w.id then return
    let rel := m.pos - w.bounds.origin
    match w.frameHit rel, w.controlAt? rel with
    | .interior, some i => withWindow w.id (·.mouseControl i (m.relativeTo w.bounds.origin))
    | _, _ => modifyDesktop (·.modify w.id (·.wheel (m.action == .wheelDown)))
  | _ => pure ()

def handleEvent : Event → AppM α Unit
  | .key k => handleKey k
  | .mouse m => handleMouse m
  | .resize w h => do
    let s : Size := ⟨w, h⟩
    modify fun st => { st with screen := s, menu := none, popup := none, capture := .none }
    modifyDesktop (·.setBounds (desktopRect s))

/-! ### Drawing -/

/-- The DOS mouse cursor: the cell's attribute XOR `0x77`. -/
def invertAttr (a : Attr) : Attr := Attr.ofByte (a.toByte ^^^ 0x77)

def render : AppM α (Screen × Option Point) := do
  let app ← read
  let st ← get
  let t := app.theme
  let s := st.screen
  let desk := desktopRect s
  let d := st.desktop
  let screen := Draw.run (Screen.new s.w s.h) do
    Draw.fill desk t.backgroundChar t.background
    Draw.clip desk do
      for h : i in [0:d.windows.size] do
        let w := d.windows[i]
        Draw.shadow w.bounds t.shadow t.shadowOnBlack
        Draw.within w.bounds (w.draw t (i + 1 == d.windows.size) (w.isMaximized desk))
    MenuBar.drawBar app.menuBar st.menu t.menu s.w
    StatusLine.draw app.statusLine app.statusHint st.statusPressed t.statusLine (s.h - 1 : Nat) s.w
    if let some track := st.menu then
      let boxes := MenuBar.boxes app.menuBar track s
      for h : k in [0:boxes.size] do
        let (r, items) := boxes[k]
        MenuBar.drawBox r items track.path[k]? t
    if let some p := st.popup then p.draw t
  let screen := match app.mouseCursor, st.mouse with
    | true, some p => screen.modify p.x p.y fun c => { c with attr := invertAttr c.attr }
    | _, _ => screen
  let cursor : Option Point :=
    if st.menu.isSome || st.popup.isSome then none
    else d.top? >>= fun w => (w.cursorPos?.map (· + w.bounds.origin)).filter desk.contains
  return (screen, cursor)

/-! ### Main loop -/

/--
Runs the application until a `quit` command. `windows` are opened in order, so the
last one starts out active.
-/
def run (app : App α) (windows : Array (Window α)) : IO Unit := do
  let mode ← Terminal.detectColorMode
  Terminal.withTerminal app.mouseCursor do
    let (w, h) ← Terminal.size
    let screen : Size := ⟨w, h⟩
    let desktop := windows.foldl Desktop.insert ({ bounds := desktopRect screen } : Desktop α)
    let mut st : AppState α := { desktop, screen }
    let mut prev : Option Screen := none
    let mut pending := ByteArray.empty
    let mut dirty := true
    repeat
      if dirty then
        let ((frame, cursor), _) ← (render.run app).run st
        Terminal.writeString (Terminal.diff mode prev frame cursor)
        prev := some frame
        dirty := false
      let bytes ← Terminal.read (if pending.isEmpty then 100 else 25)
      let (evs, rest) :=
        if bytes.isEmpty then Input.decode pending (flush := true)
        else Input.decode (pending ++ bytes)
      pending := rest
      let (w', h') ← Terminal.size
      let evs := if w' != st.screen.w || h' != st.screen.h then evs.push (.resize w' h') else evs
      for ev in evs do
        st := (← ((handleEvent ev).run app).run st).2
        dirty := true
      if st.quit then break

end App

end HyperVision
