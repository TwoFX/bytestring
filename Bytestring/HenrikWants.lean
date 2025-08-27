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

end ByteOffset

deriving instance DecidableEq for ByteString.Pos

namespace Slice

theorem prev_ne_endPos {s : Slice} {p : s.Pos} (h : p ≠ s.startPos) : p.prev h ≠ s.endPos := sorry

end Slice
end ByteString
