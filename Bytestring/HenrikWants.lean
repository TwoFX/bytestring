import Bytestring.Basic

namespace UInt8

def toAsciiLower (b : UInt8) : UInt8 :=
  -- TODO: can do better than this with bitmasking
  if b >= 65 && b <= 90 then (b + 32) else b

end UInt8

namespace ByteString

namespace ByteOffset

instance : Inhabited ByteOffset := ⟨0⟩

instance : DecidableLE ByteString.ByteOffset :=
  inferInstanceAs (∀ a b : ByteString.ByteOffset, Decidable (a.numBytes ≤ b.numBytes))

@[inline]
def inc (offset : ByteOffset) : ByteOffset := ⟨offset.numBytes + 1⟩

@[inline]
def dec (offset : ByteOffset) : ByteOffset := ⟨offset.numBytes - 1⟩

def findNextPos (offset : ByteOffset) (s : Slice) (h : offset < s.utf8Size) : s.Pos :=
  if (s.utf8ByteAt offset h).isUtf8FirstByte then
    go offset.inc
  else
    go offset
where
  go (offset : ByteOffset) : s.Pos :=
    if h : offset < s.utf8Size then
      if (s.utf8ByteAt offset h).isUtf8FirstByte then
        s.pos! offset
      else
        go offset.inc
    else
      s.endPos
  termination_by s.utf8Size.numBytes - offset.numBytes
  decreasing_by sorry

end ByteOffset

deriving instance DecidableEq for ByteString.Pos

def Pos.prev {s : ByteString} (pos : s.Pos) (h : pos ≠ s.startPos) : s.Pos := sorry

@[inline]
def Pos.prev? {s : ByteString} (p : s.Pos) : Option s.Pos :=
  if h : p = s.startPos then
    none
  else
    some (p.prev h)

opaque _root_.Char.isAscii : Char → Bool

def setAscii (s : ByteString) (p : s.Pos) {h1 : p ≠ s.endPos} (h2 : (p.get h1).isAscii)
    (c : Char) (h3 : c.isAscii) : ByteString := sorry

namespace Slice

theorem prev_ne_endPos {s : Slice} {p : s.Pos} (h : p ≠ s.startPos) : p.prev h ≠ s.endPos := sorry

namespace Pos

def nextn {s : Slice} (p : s.Pos) (n : Nat) : s.Pos :=
  match n with
  | 0 => p
  | n + 1 =>
    if h : p ≠ s.endPos then
      nextn (p.next h) n
    else
      p

def prevn {s : Slice} (p : s.Pos) (n : Nat) : s.Pos :=
  match n with
  | 0 => p
  | n + 1 =>
    if h : p ≠ s.startPos then
      nextn (p.prev h) n
    else
      p

@[inline]
def prev? {s : Slice} (p : s.Pos) : Option s.Pos :=
  if h : p = s.startPos then
    none
  else
    some (p.prev h)

end Pos

end Slice
end ByteString
