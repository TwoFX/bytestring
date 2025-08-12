import Bytestring.ByteArray

def List.utf8Encode (l : List Char) : ByteArray :=
  l.flatMap String.utf8EncodeChar |>.toByteArray

@[simp]
theorem List.utf8Encode_nil : List.utf8Encode [] = ByteArray.empty := by simp [utf8Encode]

theorem List.utf8Encode_singleton {c : Char} : [c].utf8Encode = (String.utf8EncodeChar c).toByteArray := by
  simp [utf8Encode]

@[simp]
theorem List.utf8Encode_append {l l' : List Char} :
    (l ++ l').utf8Encode = l.utf8Encode ++ l'.utf8Encode := by
  simp [utf8Encode]

structure IsValidUtf8 (b : ByteArray) : Prop where
  exists_model : ∃ m, b = List.utf8Encode m

theorem isValidUtf8_utf8Encode {l : List Char} : IsValidUtf8 l.utf8Encode where
  exists_model := ⟨l, rfl⟩

theorem isValidUtf8_empty : IsValidUtf8 ByteArray.empty where
  exists_model := ⟨[], by simp⟩

theorem isValidUtf8_toByteArray_utf8EncodeChar {c : Char} :
    IsValidUtf8 (String.utf8EncodeChar c).toByteArray where
  exists_model := ⟨[c], by simp [List.utf8Encode_singleton]⟩

theorem IsValidUtf8.append {b b' : ByteArray} (h : IsValidUtf8 b) (h' : IsValidUtf8 b') :
    IsValidUtf8 (b ++ b') := by
  rcases h with ⟨m, rfl⟩
  rcases h' with ⟨m', rfl⟩
  exact ⟨⟨m ++ m', by simp⟩⟩

@[ext]
structure ByteString where
  bytes : ByteArray
  isValidUtf8 : IsValidUtf8 bytes

def ByteString.empty : ByteString where
  bytes := ByteArray.empty
  isValidUtf8 := isValidUtf8_empty

@[simp]
theorem ByteString.bytes_empty : ByteString.empty.bytes = ByteArray.empty := rfl

def ByteString.utf8Size (s : ByteString) : Nat :=
  s.bytes.size

@[simp]
theorem ByteString.size_bytes {s : ByteString} : s.bytes.size = s.utf8Size := rfl

@[simp]
theorem ByteString.utf8Size_empty : ByteString.empty.utf8Size = 0 := by
  simp [← ByteString.size_bytes]

@[simp]
theorem ByteString.utf8Size_eq_zero_iff {s : ByteString} : s.utf8Size = 0 ↔ s = ByteString.empty := by
  refine ⟨fun h => ?_, fun h => h ▸ ByteString.utf8Size_empty⟩
  ext1
  simp [← ByteArray.size_eq_zero_iff, h]

def ByteString.append (s t : ByteString) : ByteString where
  bytes := s.bytes ++ t.bytes
  isValidUtf8 := s.isValidUtf8.append t.isValidUtf8

def ByteString.utf8ByteAt (s : ByteString) (byteIdx : Nat) (h : byteIdx < s.utf8Size) : UInt8 :=
  s.bytes[byteIdx]

instance : Append ByteString where
  append s t := s.append t

@[simp]
theorem ByteString.bytes_append {s t : ByteString} : (s ++ t).bytes = s.bytes ++ t.bytes := by
  rfl

@[simp]
theorem ByteString.utf8Size_append {s t : ByteString} : (s ++ t).utf8Size = s.utf8Size + t.utf8Size := by
  simp [← size_bytes]

@[simp]
theorem ByteString.empty_append {s : ByteString} : ByteString.empty ++ s = s := by
  ext1
  simp

@[simp]
theorem ByteString.append_empty {s : ByteString} : s ++ ByteString.empty = s := by
  ext1
  simp

structure ByteString.ValidPos (s : ByteString) (byteIdx : Nat) : Prop where
  exists_prefix : ∃ t₁ t₂ : ByteString, s = t₁ ++ t₂ ∧ byteIdx = t₁.utf8Size

@[simp, grind]
theorem ByteString.validPos_zero {s : ByteString} : s.ValidPos 0 where
  exists_prefix := ⟨ByteString.empty, s, by simp, by simp⟩

@[simp, grind]
theorem ByteString.validPos_empty {byteIdx : Nat} :
    ByteString.empty.ValidPos byteIdx ↔ byteIdx = 0 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨t₁, t₂, ht, rfl⟩
    have := congrArg ByteString.utf8Size ht
    simp only [utf8Size_empty, utf8Size_append] at this
    omega
  · rintro rfl
    simp

@[simp, grind]
theorem ByteString.validPos_utf8size {s : ByteString} : s.ValidPos s.utf8Size where
  exists_prefix := ⟨s, ByteString.empty, by simp, by simp⟩

def UInt8.IsUtf8FirstByte (c : UInt8) : Prop :=
  c &&& 0x80 = 0 ∨ c &&& 0xe0 = 0xc0 ∨ c &&& 0xf0 = 0xe0 ∨ c &&& 0xf8 = 0xf0

def List.toByteString (l : List Char) : ByteString where
  bytes := l.utf8Encode
  isValidUtf8 := ⟨⟨l, rfl⟩⟩

@[simp] theorem List.bytes_toByteString {l : List Char} : l.toByteString.bytes = l.utf8Encode := rfl

@[simp]
theorem List.toByteString_nil : List.toByteString [] = ByteString.empty := by
  ext1
  simp

theorem ByteString.exists_eq_toByteString (s : ByteString) :
    ∃ l : List Char, s = l.toByteString := by
  rcases s with ⟨_, ⟨⟨l, rfl⟩⟩⟩
  refine ⟨l, rfl⟩

def ByteString.push (b : ByteString) (c : Char) : ByteString where
  bytes := b.bytes ++ [c].utf8Encode
  isValidUtf8 := by
    obtain ⟨l, rfl⟩ := b.exists_eq_toByteString
    rw [List.bytes_toByteString, ← List.utf8Encode_append]
    apply isValidUtf8_utf8Encode

@[simp]
theorem ByteString.bytes_push {s : ByteString} {c : Char} : (s.push c).bytes = s.bytes ++ [c].utf8Encode := rfl

@[simp]
theorem ByteString.utf8Size_push {s : ByteString} {c : Char} : (s.push c).utf8Size = s.utf8Size + c.utf8Size := by
  simp [← size_bytes, List.utf8Encode_singleton]

@[simp]
theorem ByteString.append_toByteString_singleton {s : ByteString} {c : Char} :
    s ++ [c].toByteString = s.push c := by
  ext1
  simp

def ByteString.singleton (c : Char) : ByteString :=
  ByteString.empty.push c

@[simp]
theorem ByteString.bytes_singleton {c : Char} : (ByteString.singleton c).bytes = [c].utf8Encode := by
  simp [singleton]

@[simp, grind]
theorem ByteString.utf8size_singleton {c : Char} : (ByteString.singleton c).utf8Size = c.utf8Size := by
  simp [singleton]

theorem isUtf8FirstByte_getElem_utf8Encode_singleton {c : Char} {i : Nat} {hi : i < [c].utf8Encode.size} :
    UInt8.IsUtf8FirstByte [c].utf8Encode[i] ↔ i = 0 := sorry

theorem ByteString.validPos_singleton {c : Char} {byteIdx : Nat} :
    (ByteString.singleton c).ValidPos byteIdx ↔ byteIdx = 0 ∨ byteIdx = c.utf8Size := by
  refine ⟨?_, ?_⟩
  

@[simp]
theorem ByteString.append_singleton {s : ByteString} {c : Char} :
    s ++ ByteString.singleton c = s.push c := by
  ext1
  simp

theorem ByteString.validPos_append {s t : ByteString} {byteIdx : Nat} :
    (s ++ t).ValidPos byteIdx ↔ s.ValidPos byteIdx ∨ (s.utf8Size ≤ byteIdx ∧ t.ValidPos (byteIdx - s.utf8Size)) := sorry

set_option grind.warning false

theorem ByteString.validPos_push {s : ByteString} {c : Char} {byteIdx : Nat} :
    (s.push c).ValidPos byteIdx ↔ s.ValidPos byteIdx ∨ byteIdx = (s.push c).utf8Size := by
  rw [← append_singleton, validPos_append, validPos_singleton, utf8Size_append]
  grind

theorem ByteString.push_induction (s : ByteString) (motive : ByteString → Prop) (empty : motive ByteString.empty)
    (push : ∀ b c, motive b → motive (b.push c)) : motive s := sorry

-- theorem isUtf8FirstByte_getElem_utf8EncodeChar (c : Char) (i : Nat) (hi : i < (String.utf8EncodeChar c).length) :
--     UInt8.IsUtf8FirstByte (String.utf8EncodeChar c)[i] ↔ i = 0 := sorry

theorem ByteString.validPos_iff_isUtf8FirstByte (s : ByteString) (byteIdx : Nat) :
    s.ValidPos byteIdx ↔
      (byteIdx = s.utf8Size ∨ (∃ (h : byteIdx < s.utf8Size), UInt8.IsUtf8FirstByte (s.utf8ByteAt byteIdx h))) := by
  induction s using ByteString.push_induction with
  | empty => simp
  | push s c ih =>
    rw [validPos_push, ih]
    refine ⟨?_, ?_⟩
    · rintro ((rfl|⟨h, hb⟩)|h)
      · refine Or.inr ⟨by simp [Char.utf8Size_pos], ?_⟩
        simp only [utf8ByteAt, bytes_push, ← size_bytes]
        rw [ByteArray.getElem_append_right (Nat.le_refl _)]
        simp [isUtf8FirstByte_getElem_utf8Encode_singleton]
      · refine Or.inr ⟨by simp; omega, ?_⟩
        simp only [utf8ByteAt, bytes_push]
        rwa [ByteArray.getElem_append_left, ← utf8ByteAt]
      · exact Or.inl h
    · rintro (h|⟨h, hb⟩)
      · exact Or.inr h
      · simp only [utf8ByteAt, bytes_push] at hb
        by_cases h' : byteIdx < s.utf8Size
        · refine Or.inl (Or.inr ⟨h', ?_⟩)
          rwa [ByteArray.getElem_append_left h', ← utf8ByteAt] at hb
        · refine Or.inl (Or.inl ?_)
          rw [ByteArray.getElem_append_right (by simp; omega)] at hb
          simp [isUtf8FirstByte_getElem_utf8Encode_singleton] at hb
          omega
