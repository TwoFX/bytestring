import Bytestring.ByteArray

def List.utf8Encode (l : List Char) : ByteArray :=
  l.flatMap String.utf8EncodeChar |>.toByteArray

@[simp]
theorem List.utf8Encode_append {l l' : List Char} :
    (l ++ l').utf8Encode = l.utf8Encode ++ l'.utf8Encode := by
  simp [utf8Encode]

structure IsValidUtf8 (b : ByteArray) : Prop where
  exists_model : ∃ m, b = List.utf8Encode m

theorem IsValidUtf8.append {b b' : ByteArray} (h : IsValidUtf8 b) (h' : IsValidUtf8 b') :
    IsValidUtf8 (b ++ b') := by
  rcases h with ⟨m, rfl⟩
  rcases h' with ⟨m', rfl⟩
  exact ⟨⟨m ++ m', by simp⟩⟩

structure ByteString where
  bytes : ByteArray
  isValidUtf8 : IsValidUtf8 bytes

def ByteString.utf8Size (s : ByteString) : Nat :=
  s.bytes.size

def ByteString.append (s t : ByteString) : ByteString where
  bytes := s.bytes ++ t.bytes
  isValidUtf8 := s.isValidUtf8.append t.isValidUtf8

def ByteString.utf8ByteAt (s : ByteString) (byteIdx : Nat) (h : byteIdx < s.utf8Size) : UInt8 :=
  s.bytes[byteIdx]

instance : Append ByteString where
  append s t := s.append t

structure ByteString.ValidPos (s : ByteString) (byteIdx : Nat) : Prop where
  exists_prefix : ∃ t₁ t₂ : ByteString, s = t₁ ++ t₂ ∧ byteIdx = t₁.utf8Size

def UInt8.IsUtf8FirstByte (c : UInt8) : Prop :=
  c &&& 0x80 = 0 ∨ c &&& 0xe0 = 0xc0 ∨ c &&& 0xf0 = 0xe0 ∨ c &&& 0xf8 = 0xf0

theorem ByteString.validPos_iff_isUtf8FirstByte (s : ByteString) (byteIdx : Nat) :
    s.ValidPos byteIdx ↔
      (byteIdx = s.utf8Size ∨ (∃ (h : byteIdx < s.utf8Size), UInt8.IsUtf8FirstByte (s.utf8ByteAt byteIdx h))) := by
  sorry
