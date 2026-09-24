/-!
# Colors

The sixteen CGA text-mode colors and foreground/background attribute pairs.
Colors are emitted as 24-bit RGB so the classic palette looks the same in every
terminal, regardless of the user's terminal theme.
-/

namespace HyperVision

/-- The sixteen CGA colors, in hardware order. -/
inductive Color where
  | black | blue | green | cyan | red | magenta | brown | lightGray
  | darkGray | lightBlue | lightGreen | lightCyan | lightRed | lightMagenta | yellow | white
deriving DecidableEq, Repr, Inhabited, Hashable

namespace Color

/-- The hardware index of a color (0‥15). -/
def index : Color → Fin 16
  | black => 0 | blue => 1 | green => 2 | cyan => 3
  | red => 4 | magenta => 5 | brown => 6 | lightGray => 7
  | darkGray => 8 | lightBlue => 9 | lightGreen => 10 | lightCyan => 11
  | lightRed => 12 | lightMagenta => 13 | yellow => 14 | white => 15

/-- Inverse of `index`. -/
def ofIndex (i : Fin 16) : Color :=
  #[black, blue, green, cyan, red, magenta, brown, lightGray,
    darkGray, lightBlue, lightGreen, lightCyan, lightRed, lightMagenta, yellow, white][i]

/-- The exact RGB values of the IBM CGA palette. -/
def rgb : Color → UInt8 × UInt8 × UInt8
  | black => (0x00, 0x00, 0x00)
  | blue => (0x00, 0x00, 0xAA)
  | green => (0x00, 0xAA, 0x00)
  | cyan => (0x00, 0xAA, 0xAA)
  | red => (0xAA, 0x00, 0x00)
  | magenta => (0xAA, 0x00, 0xAA)
  | brown => (0xAA, 0x55, 0x00)
  | lightGray => (0xAA, 0xAA, 0xAA)
  | darkGray => (0x55, 0x55, 0x55)
  | lightBlue => (0x55, 0x55, 0xFF)
  | lightGreen => (0x55, 0xFF, 0x55)
  | lightCyan => (0x55, 0xFF, 0xFF)
  | lightRed => (0xFF, 0x55, 0x55)
  | lightMagenta => (0xFF, 0x55, 0xFF)
  | yellow => (0xFF, 0xFF, 0x55)
  | white => (0xFF, 0xFF, 0xFF)

/-- The ANSI SGR color number (0‥7) and brightness, for 16-color terminals. -/
def ansi : Color → Nat × Bool
  | black => (0, false) | blue => (4, false) | green => (2, false) | cyan => (6, false)
  | red => (1, false) | magenta => (5, false) | brown => (3, false) | lightGray => (7, false)
  | darkGray => (0, true) | lightBlue => (4, true) | lightGreen => (2, true)
  | lightCyan => (6, true) | lightRed => (1, true) | lightMagenta => (5, true)
  | yellow => (3, true) | white => (7, true)

/-- The closest entry of the fixed xterm 256-color cube. -/
def xterm256 : Color → Nat
  | black => 16 | blue => 19 | green => 34 | cyan => 37
  | red => 124 | magenta => 127 | brown => 130 | lightGray => 145
  | darkGray => 59 | lightBlue => 63 | lightGreen => 83 | lightCyan => 87
  | lightRed => 203 | lightMagenta => 207 | yellow => 227 | white => 231

theorem ofIndex_index (c : Color) : ofIndex c.index = c := by
  cases c <;> rfl

end Color

/-- A text attribute: foreground and background color. -/
structure Attr where
  fg : Color
  bg : Color
deriving DecidableEq, Repr, Inhabited, Hashable

namespace Attr

/-- Decodes a DOS attribute byte `0xBF` (background in the high nibble). -/
def ofByte (b : UInt8) : Attr :=
  ⟨Color.ofIndex ⟨b.toNat % 16, Nat.mod_lt _ (by decide)⟩,
   Color.ofIndex ⟨b.toNat / 16 % 16, Nat.mod_lt _ (by decide)⟩⟩

/-- Encodes the attribute as a DOS attribute byte. -/
def toByte (a : Attr) : UInt8 :=
  (a.bg.index.val * 16 + a.fg.index.val).toUInt8

/-- Same colors with the foreground replaced. -/
def withFg (a : Attr) (fg : Color) : Attr := { a with fg }

end Attr

end HyperVision
