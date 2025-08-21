import Bytestring.Bootstrap.ByteArray

def List.utf8Encode (l : List Char) : ByteArray :=
  l.flatMap String.utf8EncodeChar |>.toByteArray

structure IsValidUtf8 (b : ByteArray) : Prop where
  exists_model : ∃ m, b = List.utf8Encode m

@[simp]
theorem IsValidUtf8.empty : IsValidUtf8 ByteArray.empty where
  exists_model := ⟨[], rfl⟩

@[ext]
structure ByteString where
  bytes : ByteArray
  isValidUtf8 : IsValidUtf8 bytes

structure ByteString.ByteOffset where
  numBytes : Nat

def ByteString.utf8Size (s : ByteString) : ByteString.ByteOffset :=
  ⟨s.bytes.size⟩

instance : LE ByteString.ByteOffset where
  le a b := a.numBytes ≤ b.numBytes

theorem ByteString.ByteOffset.le_iff_numBytes_le {a b : ByteString.ByteOffset} :
    a ≤ b ↔ a.numBytes ≤ b.numBytes := Iff.rfl

@[simp]
theorem ByteString.numBytes_utf8Size (s : ByteString) :
  s.utf8Size.numBytes = s.bytes.size := rfl

structure ByteString.ValidOffset (s : ByteString) (off : ByteOffset) where
  le_utf8Size : off ≤ s.utf8Size
  isValidUtf8 : IsValidUtf8 (s.bytes.extract 0 off.numBytes)

structure ByteString.Pos (s : ByteString) where
  offset : ByteOffset
  validOffset : s.ValidOffset offset

def ByteString.startPos (s : ByteString) : s.Pos where
  offset := ⟨0⟩
  validOffset := ⟨by simp [ByteOffset.le_iff_numBytes_le], by simp⟩

def ByteString.endPos (s : ByteString) : s.Pos where
  offset := s.utf8Size
  validOffset := ⟨by simp [ByteOffset.le_iff_numBytes_le], by simpa using s.isValidUtf8⟩

structure ByteString.Slice where
  str : ByteString
  startInclusive : str.Pos
  endExclusive : str.Pos
  startInclusive_le_endExclusive : startInclusive.offset ≤ endExclusive.offset

def ByteString.toSlice (s : ByteString) : ByteString.Slice where
  str := s
  startInclusive := s.startPos
  endExclusive := s.endPos
  startInclusive_le_endExclusive := by
    simp [ByteString.ByteOffset.le_iff_numBytes_le, startPos]
