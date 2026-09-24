import HyperVision.Color

/-!
# Theme

The default theme reproduces Turbo Vision's `cpAppColor` palette. Instead of the
original chains of palette indices, every view reads named, typed fields.
-/

namespace HyperVision

/-- Colors of the menu bar, drop-down menus and the status line. -/
structure MenuColors where
  normal : Attr
  disabled : Attr
  shortcut : Attr
  selected : Attr
  selectedDisabled : Attr
  selectedShortcut : Attr
deriving Repr, Inhabited

/-- Colors of a window frame. -/
structure FrameColors where
  passive : Attr
  active : Attr
  /-- Close/zoom/resize icons; also the whole frame while it is being dragged. -/
  icon : Attr
deriving Repr, Inhabited

/-- Colors of one window class (blue, cyan or gray). -/
structure WindowColors where
  frame : FrameColors
  scrollPage : Attr
  scrollControls : Attr
  text : Attr
  selection : Attr
deriving Repr, Inhabited

/-- Colors of dialog boxes and the controls inside them. -/
structure DialogColors where
  frame : FrameColors
  scrollPage : Attr
  scrollControls : Attr
  staticText : Attr
  label : Attr
  labelSelected : Attr
  labelShortcut : Attr
  button : Attr
  buttonDefault : Attr
  buttonSelected : Attr
  buttonDisabled : Attr
  buttonShortcut : Attr
  buttonShadow : Attr
  cluster : Attr
  clusterSelected : Attr
  clusterShortcut : Attr
  clusterDisabled : Attr
  input : Attr
  inputSelection : Attr
  inputArrows : Attr
  historyArrow : Attr
  historySides : Attr
  listNormal : Attr
  listFocused : Attr
  listSelected : Attr
  listDivider : Attr
deriving Repr, Inhabited

/-- Colors of the drop-down list opened from a combo box (Turbo Vision's history window). -/
structure PopupColors where
  frame : Attr
  icon : Attr
  item : Attr
  focused : Attr
  scrollPage : Attr
  scrollControls : Attr
deriving Repr, Inhabited

structure Theme where
  background : Attr
  backgroundChar : Char
  menu : MenuColors
  statusLine : MenuColors
  blueWindow : WindowColors
  cyanWindow : WindowColors
  grayWindow : WindowColors
  dialog : DialogColors
  popup : PopupColors
  /-- Applied to the cells under a drop shadow (their characters are kept). -/
  shadow : Attr
  /-- Shadow attribute used where the background is already black. -/
  shadowOnBlack : Attr
deriving Repr, Inhabited

namespace Theme

private abbrev a (b : UInt8) : Attr := Attr.ofByte b

private def menuColors : MenuColors :=
  { normal := a 0x70, disabled := a 0x78, shortcut := a 0x74
    selected := a 0x20, selectedDisabled := a 0x28, selectedShortcut := a 0x24 }

/-- Turbo Vision's default color palette. -/
def turboVision : Theme where
  background := a 0x71
  backgroundChar := '░'
  menu := menuColors
  statusLine := menuColors
  blueWindow :=
    { frame := { passive := a 0x17, active := a 0x1F, icon := a 0x1A }
      scrollPage := a 0x31, scrollControls := a 0x31, text := a 0x1E, selection := a 0x71 }
  cyanWindow :=
    { frame := { passive := a 0x37, active := a 0x3F, icon := a 0x3A }
      scrollPage := a 0x13, scrollControls := a 0x13, text := a 0x3E, selection := a 0x21 }
  grayWindow :=
    { frame := { passive := a 0x70, active := a 0x7F, icon := a 0x7A }
      scrollPage := a 0x13, scrollControls := a 0x13, text := a 0x70, selection := a 0x7F }
  dialog :=
    { frame := { passive := a 0x70, active := a 0x7F, icon := a 0x7A }
      scrollPage := a 0x13, scrollControls := a 0x13
      staticText := a 0x70
      label := a 0x70, labelSelected := a 0x7F, labelShortcut := a 0x7E
      button := a 0x20, buttonDefault := a 0x2B, buttonSelected := a 0x2F
      buttonDisabled := a 0x78, buttonShortcut := a 0x2E, buttonShadow := a 0x70
      cluster := a 0x30, clusterSelected := a 0x3F, clusterShortcut := a 0x3E
      clusterDisabled := a 0x38
      input := a 0x1F, inputSelection := a 0x2F, inputArrows := a 0x1A
      historyArrow := a 0x20, historySides := a 0x72
      listNormal := a 0x30, listFocused := a 0x2F, listSelected := a 0x3E, listDivider := a 0x31 }
  popup :=
    { frame := a 0x1F, icon := a 0x1A, item := a 0x1F, focused := a 0x2F
      scrollPage := a 0x31, scrollControls := a 0x72 }
  shadow := a 0x08
  shadowOnBlack := a 0x80

instance : Inhabited Theme := ⟨turboVision⟩

end Theme

end HyperVision
