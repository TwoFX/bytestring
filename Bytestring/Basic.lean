import Bytestring.ByteArray
import Bytestring.Decode

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

@[simp]
theorem String.utf8EncodeChar_ne_nil {c : Char} : String.utf8EncodeChar c ≠ [] := by
  grind [String.utf8EncodeChar]

@[simp]
theorem List.utf8Encode_eq_empty {l : List Char} : l.utf8Encode = ByteArray.empty ↔ l = [] := by
  simp [utf8Encode, ← List.eq_nil_iff_forall_not_mem]

theorem utf8DecodeChar?_utf8Encode_singleton_append {b : ByteArray} {c : Char} :
    utf8DecodeChar? ([c].utf8Encode ++ b) 0 = some c := by
  rw [List.utf8Encode, List.flatMap_cons, List.toByteArray_append,
    List.flatMap_nil, List.toByteArray_nil, ByteArray.append_empty,
    utf8DecodeChar?_utf8EncodeChar_append]

theorem utf8DecodeChar?_utf8Encode_cons {l : List Char} {c : Char} :
    utf8DecodeChar? (c::l).utf8Encode 0 = some c := by
  rw [List.utf8Encode, List.flatMap_cons, List.toByteArray_append,
    utf8DecodeChar?_utf8EncodeChar_append]

structure IsValidUtf8 (b : ByteArray) : Prop where
  exists_model : ∃ m, b = List.utf8Encode m

theorem isValidUtf8_utf8Encode {l : List Char} : IsValidUtf8 l.utf8Encode where
  exists_model := ⟨l, rfl⟩

@[simp]
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

@[simp]
theorem List.head_cons_tail {l : List α} (h : l ≠ []) : l.head h :: l.tail = l := by
  cases l <;> grind

theorem isValidUtf8_utf8Encode_singleton_append_iff {b : ByteArray} {c : Char} :
    IsValidUtf8 ([c].utf8Encode ++ b) ↔ IsValidUtf8 b := by
  refine ⟨?_, fun h => IsValidUtf8.append isValidUtf8_utf8Encode h⟩
  rintro ⟨⟨l, hl⟩⟩
  match l with
  | [] => simp at hl
  | d::l =>
    obtain rfl : c = d := by
      replace hl := congrArg (fun l => utf8DecodeChar? l 0) hl
      simpa [utf8DecodeChar?_utf8Encode_singleton_append,
        utf8DecodeChar?_utf8Encode_cons] using hl
    rw [← List.singleton_append (l := l), List.utf8Encode_append,
      ByteArray.append_right_inj] at hl
    exact hl ▸ isValidUtf8_utf8Encode

def ByteArray.utf8Decode? (b : ByteArray) : Option (Array Char) :=
  go 0 (by simp) #[]
where
  go (i : Nat) (hi : i ≤ b.size) (acc : Array Char) : Option (Array Char) :=
    if i = b.size then
      some acc
    else
      match h : utf8DecodeChar? b i with
      | none => none
      | some c => go (i + c.utf8Size) (le_size_of_utf8DecodeChar?_eq_some hi h) (acc.push c)
  termination_by b.size - i
  decreasing_by grind [Char.utf8Size_pos]

@[simp]
theorem ByteArray.utf8Decode?_empty : ByteArray.empty.utf8Decode? = some #[] := by
  simp [utf8Decode?, utf8Decode?.go]

theorem ByteArray.isSome_utf8Decode?go_iff {b : ByteArray} {i : Nat} {hi : i ≤ b.size} {acc : Array Char} :
    (ByteArray.utf8Decode?.go b i hi acc).isSome ↔ IsValidUtf8 (b.extract i b.size) := by
  fun_induction ByteArray.utf8Decode?.go with
  | case1 => simp
  | case2 i hi acc h₁ h₂ =>
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨⟨l, hl⟩⟩
    have : l ≠ [] := by
      rintro rfl
      simp at hl
      omega
    rw [← l.head_cons_tail this] at hl
    rw [utf8DecodeChar?_eq_utf8DecodeChar?_drop, hl, utf8DecodeChar?_utf8Encode_cons] at h₂
    simp at h₂
  | case3 i hi acc h₁ c h₂ ih =>
    rw [ih]
    have h₂' := h₂
    rw [utf8DecodeChar?_eq_utf8DecodeChar?_drop] at h₂'
    obtain ⟨l, hl⟩ := exists_of_utf8DecodeChar?_eq_some h₂'
    rw [ByteArray.extract_eq_extract_append_extract (i := i) (i + c.utf8Size) (by omega)
      (le_size_of_utf8DecodeChar?_eq_some hi h₂)] at hl ⊢
    rw [ByteArray.append_inj_left hl (by have := le_size_of_utf8DecodeChar?_eq_some hi h₂; simp; omega),
      ← List.utf8Encode_singleton, isValidUtf8_utf8Encode_singleton_append_iff]

theorem ByteArray.isSome_utf8Decode?_iff {b : ByteArray} :
    b.utf8Decode?.isSome ↔ IsValidUtf8 b := by
  rw [utf8Decode?, isSome_utf8Decode?go_iff, extract_zero_size]

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

def List.toByteString (l : List Char) : ByteString where
  bytes := l.utf8Encode
  isValidUtf8 := ⟨⟨l, rfl⟩⟩

@[simp] theorem List.bytes_toByteString {l : List Char} : l.toByteString.bytes = l.utf8Encode := rfl

@[simp]
theorem List.toByteString_nil : List.toByteString [] = ByteString.empty := by
  ext1
  simp

@[simp]
theorem List.toByteString_append {l₁ l₂ : List Char} : (l₁ ++ l₂).toByteString = l₁.toByteString ++ l₂.toByteString := by
  ext1
  simp

def ByteString.toCharArray (b : ByteString) : Array Char :=
  b.bytes.utf8Decode?.get (b.bytes.isSome_utf8Decode?_iff.2 b.isValidUtf8)

@[simp]
theorem ByteString.toCharArray_empty : ByteString.empty.toCharArray = #[] := by
  simp [toCharArray]

def ByteString.data (b : ByteString) : List Char :=
  b.toCharArray.toList

@[simp]
theorem ByteString.data_empty : ByteString.empty.data = [] := by
  simp [data]

def ByteString.length (b : ByteString) : Nat :=
  b.toCharArray.size

@[simp]
theorem ByteString.size_toCharArray {b : ByteString} :
    b.toCharArray.size = b.length := rfl

@[simp]
theorem ByteString.length_data {b : ByteString} :
    b.data.length = b.length := rfl

-- theorem ByteArray.utf8Decode?go_eq_utf8Decode?go_extract {b : ByteArray} {i : Nat} {hi : i ≤ b.size} {acc : Array Char} :
--     utf8Decode?.go b i hi acc = (utf8Decode?.go (b.extract i b.size) 0 (by simp) #[]).map (acc ++ ·) := by
--   fun_induction utf8Decode?.go b i hi acc with
--   | case1 => simp [utf8Decode?.go]
--   | case2 i hi acc h₁ h₂ =>
--     rw [utf8Decode?.go]
--     simp only [size_extract, Nat.le_refl, Nat.min_eq_left, Nat.zero_add, List.push_toArray,
--       List.nil_append]
--     rw [if_neg (by omega)]
--     rw [utf8DecodeChar?_eq_utf8DecodeChar?_drop] at h₂
--     split <;> simp_all
--   | case3 i hi acc h₁ c h₂ ih =>
--     rw [ih]
--     sorry

-- theorem ByteArray.utf8Decode?_utf8Encode_singleton_append {l : ByteArray} {c : Char} :
--     ([c].utf8Encode ++ l).utf8Decode? = l.utf8Decode?.map (#[c] ++ ·) := by
--   rw [utf8Decode?, utf8Decode?.go, if_neg (by simp [List.utf8Encode_singleton]; grind [Char.utf8Size_pos])]
--   split
--   · simp_all [utf8DecodeChar?_utf8Encode_singleton_append]
--   · rename_i d h
--     obtain rfl : c = d := by simpa [utf8DecodeChar?_utf8Encode_singleton_append] using h
--     rw [utf8Decode?go_eq_utf8Decode?go_extract, utf8Decode?, Nat.zero_add]
--     simp only [List.push_toArray, List.nil_append]
--     congr
--     apply extract_append_eq_right
--     simp [List.utf8Encode_singleton]

@[simp]
theorem List.data_toByteString {l : List Char} : l.toByteString.data = l := by
  induction l with
  | nil => simp
  | cons c l ih =>
    sorry

@[simp]
theorem ByteString.toByteString_data {b : ByteString} : b.data.toByteString = b := by
  sorry

theorem List.toByteString_injective {l₁ l₂ : List Char} (h : l₁.toByteString = l₂.toByteString) : l₁ = l₂ := by
  simpa using congrArg ByteString.data h

@[simp]
theorem ByteString.data_append {l₁ l₂ : ByteString} : (l₁ ++ l₂).data = l₁.data ++ l₂.data := by
  apply List.toByteString_injective
  simp

@[simp]
theorem ByteString.utf8encode_data {b : ByteString} : b.data.utf8Encode = b.bytes :=
  congrArg ByteString.bytes (ByteString.toByteString_data (b := b))

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

theorem List.validPos_toByteString {l : List Char} {byteIdx : Nat} :
    l.toByteString.ValidPos byteIdx ↔ ∃ i, byteIdx = (l.take i).toByteString.utf8Size := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨t₁, t₂, ht, rfl⟩⟩
    refine ⟨t₁.length, ?_⟩
    have := congrArg ByteString.data ht
    simp at this
    subst this
    simp [← ByteString.size_toCharArray]
  · rintro ⟨i, rfl⟩
    refine ⟨⟨(l.take i).toByteString, (l.drop i).toByteString, ?_, rfl⟩⟩
    simp [← List.toByteString_append]

@[simp, grind]
theorem ByteString.validPos_utf8size {s : ByteString} : s.ValidPos s.utf8Size where
  exists_prefix := ⟨s, ByteString.empty, by simp, by simp⟩

-- theorem ByteString.validPos_iff_isValidUtf8 {s : ByteString} {byteIdx : Nat} (hb : byteIdx ≤ s.utf8Size) :
--     s.ValidPos byteIdx ↔ IsValidUtf8 (s.bytes.extract 0 byteIdx) := sorry

def UInt8.IsUtf8FirstByte (c : UInt8) : Prop :=
  c &&& 0x80 = 0 ∨ c &&& 0xe0 = 0xc0 ∨ c &&& 0xf0 = 0xe0 ∨ c &&& 0xf8 = 0xf0

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

theorem ByteString.singleton_eq_toByteString {c : Char} : ByteString.singleton c = [c].toByteString := by
  ext1
  simp

theorem isUtf8FirstByte_getElem_utf8EncodeChar (c : Char) (i : Nat) (hi : i < (String.utf8EncodeChar c).length) :
    UInt8.IsUtf8FirstByte (String.utf8EncodeChar c)[i] ↔ i = 0 := by
  fun_cases String.utf8EncodeChar with
  | case1 v h =>
    subst v
    simp [String.utf8EncodeChar, h] at ⊢ hi
    simp [hi]
    sorry


  | case2 => sorry
  | case3 => sorry
  | case4 => sorry


theorem isUtf8FirstByte_getElem_utf8Encode_singleton {c : Char} {i : Nat} {hi : i < [c].utf8Encode.size} :
    UInt8.IsUtf8FirstByte [c].utf8Encode[i] ↔ i = 0 := by
  simp [List.utf8Encode_singleton, isUtf8FirstByte_getElem_utf8EncodeChar]

theorem ByteString.validPos_singleton {c : Char} {byteIdx : Nat} :
    (ByteString.singleton c).ValidPos byteIdx ↔ byteIdx = 0 ∨ byteIdx = c.utf8Size := by
  rw [singleton_eq_toByteString, List.validPos_toByteString]
  refine ⟨?_, ?_⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨rfl, hi⟩ : i = 0 ∨ 1 ≤ i := by omega
    · simp
    · rw [List.take_of_length_le (by simpa)]
      simp [← singleton_eq_toByteString]
  · rintro (rfl|rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp [← singleton_eq_toByteString]⟩

@[simp]
theorem ByteString.append_singleton {s : ByteString} {c : Char} :
    s ++ ByteString.singleton c = s.push c := by
  ext1
  simp

theorem List.take_eq_take_min {l : List α} {i : Nat} : l.take i = l.take (min i l.length) := by
  simp [List.take_eq_take_iff]

theorem ByteString.validPos_append {s t : ByteString} {byteIdx : Nat} :
    (s ++ t).ValidPos byteIdx ↔ s.ValidPos byteIdx ∨ (s.utf8Size ≤ byteIdx ∧ t.ValidPos (byteIdx - s.utf8Size)) := by
  obtain ⟨s, rfl⟩ := exists_eq_toByteString s
  obtain ⟨t, rfl⟩ := exists_eq_toByteString t
  rw [← List.toByteString_append, List.validPos_toByteString, List.validPos_toByteString, List.validPos_toByteString]
  refine ⟨?_, ?_⟩
  · rintro ⟨j, rfl⟩
    by_cases h : j ≤ s.length
    · exact Or.inl ⟨j, by simp [List.take_append_of_le_length h]⟩
    · refine Or.inr ⟨?_, ⟨j - s.length, ?_⟩⟩ <;>
        simp [List.take_append, List.take_of_length_le (i := j) (l := s) (by omega)]
  · rintro (⟨j, rfl⟩|⟨h, ⟨j, hj⟩⟩)
    · refine ⟨min j s.length, ?_⟩
      rw [List.take_append_of_le_length (Nat.min_le_right ..), ← List.take_eq_take_min]
    · refine ⟨s.length + j, ?_⟩
      simp [List.take_append, List.take_of_length_le (i := s.length + j) (l := s) (by omega)]
      omega

theorem ByteString.validPos_push {s : ByteString} {c : Char} {byteIdx : Nat} :
    (s.push c).ValidPos byteIdx ↔ s.ValidPos byteIdx ∨ byteIdx = (s.push c).utf8Size := by
  rw [← append_singleton, validPos_append, validPos_singleton, utf8Size_append]
  grind

theorem ByteString.push_induction (s : ByteString) (motive : ByteString → Prop) (empty : motive ByteString.empty)
    (push : ∀ b c, motive b → motive (b.push c)) : motive s := sorry

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
