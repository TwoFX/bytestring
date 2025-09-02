import Bytestring.Bootstrap.Basic
import Bytestring.ByteArray
import Bytestring.Decode

@[simp]
theorem List.utf8Encode_nil : List.utf8Encode [] = ByteArray.empty := by simp [utf8Encode]

theorem List.utf8Encode_singleton {c : Char} : [c].utf8Encode = (String.utf8EncodeChar c).toByteArray := by
  simp [utf8Encode]

@[simp]
theorem List.utf8Encode_append {l l' : List Char} :
    (l ++ l').utf8Encode = l.utf8Encode ++ l'.utf8Encode := by
  simp [utf8Encode]

theorem List.utf8Encode_cons {c : Char} {l : List Char} : (c :: l).utf8Encode = [c].utf8Encode ++ l.utf8Encode := by
  rw [← singleton_append, List.utf8Encode_append]

@[simp]
theorem String.utf8EncodeChar_ne_nil {c : Char} : String.utf8EncodeChar c ≠ [] := by
  grind [String.utf8EncodeChar]

@[simp]
theorem List.utf8Encode_eq_empty {l : List Char} : l.utf8Encode = ByteArray.empty ↔ l = [] := by
  simp [utf8Encode, ← List.eq_nil_iff_forall_not_mem]

@[simp]
theorem utf8DecodeChar?_utf8Encode_singleton_append {b : ByteArray} {c : Char} :
    utf8DecodeChar? ([c].utf8Encode ++ b) 0 = some c := by
  rw [List.utf8Encode, List.flatMap_cons, List.toByteArray_append,
    List.flatMap_nil, List.toByteArray_nil, ByteArray.append_empty,
    utf8DecodeChar?_utf8EncodeChar_append]

@[simp]
theorem utf8DecodeChar?_utf8Encode_singleton {c : Char} :
    utf8DecodeChar? [c].utf8Encode 0 = some c := by
  simpa using utf8DecodeChar?_utf8Encode_singleton_append (b := ByteArray.empty)

@[simp]
theorem utf8DecodeChar?_utf8Encode_cons {l : List Char} {c : Char} :
    utf8DecodeChar? (c::l).utf8Encode 0 = some c := by
  rw [List.utf8Encode, List.flatMap_cons, List.toByteArray_append,
    utf8DecodeChar?_utf8EncodeChar_append]

@[simp]
theorem utf8DecodeChar_utf8Encode_cons {l : List Char} {c : Char} {h} :
    utf8DecodeChar (c::l).utf8Encode 0 h = c := by
  simp [utf8DecodeChar]

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
      | some c => go (i + c.utf8Size) (le_size_of_utf8DecodeChar?_eq_some h) (acc.push c)
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
    rw [utf8DecodeChar?_eq_utf8DecodeChar?_extract, hl, utf8DecodeChar?_utf8Encode_cons] at h₂
    simp at h₂
  | case3 i hi acc h₁ c h₂ ih =>
    rw [ih]
    have h₂' := h₂
    rw [utf8DecodeChar?_eq_utf8DecodeChar?_extract] at h₂'
    obtain ⟨l, hl⟩ := exists_of_utf8DecodeChar?_eq_some h₂'
    rw [ByteArray.extract_eq_extract_append_extract (i := i) (i + c.utf8Size) (by omega)
      (le_size_of_utf8DecodeChar?_eq_some h₂)] at hl ⊢
    rw [ByteArray.append_inj_left hl (by have := le_size_of_utf8DecodeChar?_eq_some h₂; simp; omega),
      ← List.utf8Encode_singleton, isValidUtf8_utf8Encode_singleton_append_iff]

theorem ByteArray.isSome_utf8Decode?_iff {b : ByteArray} :
    b.utf8Decode?.isSome ↔ IsValidUtf8 b := by
  rw [utf8Decode?, isSome_utf8Decode?go_iff, extract_zero_size]

def ByteString.empty : ByteString where
  bytes := ByteArray.empty
  isValidUtf8 := isValidUtf8_empty

@[simp]
theorem ByteString.bytes_empty : ByteString.empty.bytes = ByteArray.empty := rfl

instance : Add ByteString.ByteOffset where
  add a b := ⟨a.numBytes + b.numBytes⟩

instance : Sub ByteString.ByteOffset where
  sub a b := ⟨a.numBytes - b.numBytes⟩

instance : LT ByteString.ByteOffset where
  lt a b := a.numBytes < b.numBytes

instance : DecidableLT ByteString.ByteOffset :=
  inferInstanceAs (∀ a b : ByteString.ByteOffset, Decidable (a.numBytes < b.numBytes))

@[inline]
def ByteString.Slice.utf8Size (s : ByteString.Slice) : ByteString.ByteOffset :=
  s.endExclusive.offset - s.startInclusive.offset

def ByteString.append (s t : ByteString) : ByteString where
  bytes := s.bytes ++ t.bytes
  isValidUtf8 := s.isValidUtf8.append t.isValidUtf8

instance : Append ByteString where
  append s t := s.append t

@[simp]
theorem ByteString.bytes_append {s t : ByteString} : (s ++ t).bytes = s.bytes ++ t.bytes := by
  rfl

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

theorem ByteString.exists_eq_toByteString (s : ByteString) :
    ∃ l : List Char, s = l.toByteString := by
  rcases s with ⟨_, ⟨⟨l, rfl⟩⟩⟩
  refine ⟨l, rfl⟩

theorem ByteArray.utf8Decode?go_eq_utf8Decode?go_extract {b : ByteArray} {i : Nat} {hi : i ≤ b.size} {acc : Array Char} :
    utf8Decode?.go b i hi acc = (utf8Decode?.go (b.extract i b.size) 0 (by simp) #[]).map (acc ++ ·) := by
  fun_cases utf8Decode?.go b i hi acc with
  | case1 =>
      rw [utf8Decode?.go]
      simp only [size_extract, Nat.le_refl, Nat.min_eq_left, Nat.zero_add, List.push_toArray,
        List.nil_append]
      rw [if_pos (by omega)]
      simp
  | case2 h₁ h₂ =>
    rw [utf8Decode?.go]
    simp only [size_extract, Nat.le_refl, Nat.min_eq_left, Nat.zero_add, List.push_toArray,
      List.nil_append]
    rw [if_neg (by omega)]
    rw [utf8DecodeChar?_eq_utf8DecodeChar?_extract] at h₂
    split <;> simp_all
  | case3 h₁ c h₂ =>
    conv => rhs; rw [utf8Decode?.go]
    simp only [size_extract, Nat.le_refl, Nat.min_eq_left, Nat.zero_add, List.push_toArray,
      List.nil_append]
    rw [if_neg (by omega)]
    rw [utf8DecodeChar?_eq_utf8DecodeChar?_extract] at h₂
    split
    · simp_all
    · rename_i c' hc'
      obtain rfl : c = c' := by grind
      have := c.utf8Size_pos
      conv => lhs; rw [ByteArray.utf8Decode?go_eq_utf8Decode?go_extract]
      conv => rhs; rw [ByteArray.utf8Decode?go_eq_utf8Decode?go_extract]
      simp only [size_extract, Nat.le_refl, Nat.min_eq_left, Option.map_map]
      simp only [ByteArray.extract_extract]
      simp [(by omega : i + (b.size - i) = b.size)]
      have : (fun x => acc ++ x) ∘ (fun x => #[c] ++ x) = fun x => acc.push c ++ x := by funext; simp
      simp [this]

theorem ByteArray.utf8Decode?_utf8Encode_singleton_append {l : ByteArray} {c : Char} :
    ([c].utf8Encode ++ l).utf8Decode? = l.utf8Decode?.map (#[c] ++ ·) := by
  rw [utf8Decode?, utf8Decode?.go, if_neg (by simp [List.utf8Encode_singleton]; grind [Char.utf8Size_pos])]
  split
  · simp_all [utf8DecodeChar?_utf8Encode_singleton_append]
  · rename_i d h
    obtain rfl : c = d := by simpa [utf8DecodeChar?_utf8Encode_singleton_append] using h
    rw [utf8Decode?go_eq_utf8Decode?go_extract, utf8Decode?, Nat.zero_add]
    simp only [List.push_toArray, List.nil_append]
    congr
    apply extract_append_eq_right
    simp [List.utf8Encode_singleton]

@[simp]
theorem List.utf8Decode?_utf8Encode {l : List Char} :
    l.utf8Encode.utf8Decode? = some l.toArray := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [← List.singleton_append, List.utf8Encode_append]
    simp only [ByteArray.utf8Decode?_utf8Encode_singleton_append, cons_append, nil_append,
      Option.map_eq_some_iff, Array.append_eq_toArray_iff, cons.injEq, true_and]
    refine ⟨l.toArray, ih, by simp⟩

@[simp]
theorem ByteArray.utf8Encode_get_utf8Decode? {b : ByteArray} {h} :
    (b.utf8Decode?.get h).toList.utf8Encode = b := by
  obtain ⟨l, rfl⟩ := isSome_utf8Decode?_iff.1 h
  simp

@[simp]
theorem List.data_toByteString {l : List Char} : l.toByteString.data = l := by
  simp [toByteString, ByteString.data, ByteString.toCharArray]

@[simp]
theorem ByteString.toByteString_data {b : ByteString} : b.data.toByteString = b := by
  obtain ⟨l, rfl⟩ := ByteString.exists_eq_toByteString b
  rw [List.data_toByteString]

theorem List.toByteString_injective {l₁ l₂ : List Char} (h : l₁.toByteString = l₂.toByteString) : l₁ = l₂ := by
  simpa using congrArg ByteString.data h

theorem List.toByteString_inj {l₁ l₂ : List Char} : l₁.toByteString = l₂.toByteString ↔ l₁ = l₂ :=
  ⟨toByteString_injective, (· ▸ rfl)⟩

theorem ByteString.data_injective {s₁ s₂ : ByteString} (h : s₁.data = s₂.data) : s₁ = s₂ := by
  simpa using congrArg List.toByteString h

theorem ByteString.data_inj {s₁ s₂ : ByteString} : s₁.data = s₂.data ↔ s₁ = s₂ :=
  ⟨data_injective, (· ▸ rfl)⟩

@[simp]
theorem ByteString.data_append {l₁ l₂ : ByteString} : (l₁ ++ l₂).data = l₁.data ++ l₂.data := by
  apply List.toByteString_injective
  simp

@[simp]
theorem ByteString.utf8encode_data {b : ByteString} : b.data.utf8Encode = b.bytes :=
  congrArg ByteString.bytes (ByteString.toByteString_data (b := b))

attribute [ext] ByteString.ByteOffset

instance : OfNat ByteString.ByteOffset 0 where
  ofNat := ⟨0⟩

@[simp]
theorem ByteString.ByteOffset.numBytes_zero : (0 : ByteOffset).numBytes = 0 := rfl

@[simp, grind]
theorem ByteString.validOffset_zero {s : ByteString} : s.ValidOffset 0 where
  le_utf8Size := by simp [ByteOffset.le_iff_numBytes_le]
  isValidUtf8 := by simp

@[simp]
theorem ByteString.utf8Size_empty : ByteString.empty.utf8Size = 0 := rfl

@[simp]
theorem ByteString.utf8Size_eq_zero_iff {s : ByteString} : s.utf8Size = 0 ↔ s = ByteString.empty := by
  refine ⟨fun h => ?_, fun h => h ▸ ByteString.utf8Size_empty⟩
  ext1
  simpa [← ByteArray.size_eq_zero_iff] using congrArg ByteOffset.numBytes h

theorem ByteString.extract_bytes_of_isPrefix (s : ByteString) (l : List Char) (hl : l <+: s.data) :
    s.bytes.extract 0 l.utf8Encode.size = l.utf8Encode := by
  obtain ⟨k, hk⟩ := hl
  rw [← toByteString_data (b := s), List.bytes_toByteString, ← hk, List.utf8Encode_append,
    ByteArray.extract_append_eq_left rfl]

theorem List.IsPrefix.flatMap {l₁ l₂ : List α} {f : α → List β} (h : l₁ <+: l₂) : l₁.flatMap f <+: l₂.flatMap f := by
  obtain ⟨k, rfl⟩ := h
  simp

theorem List.IsPrefix.utf8Size_toByteString_le {l₁ l₂ : List Char} (h : l₁ <+: l₂) : l₁.toByteString.utf8Size ≤ l₂.toByteString.utf8Size := by
  simp [toByteString, ByteString.utf8Size, ByteString.ByteOffset.le_iff_numBytes_le]
  simp only [utf8Encode, size_toByteArray]
  exact h.flatMap.length_le

-- -- TODO: this implementation is inefficient, the alternative is to call `Pos.next` `n` times
-- def ByteString.nthPos (s : ByteString) (n : Nat) (_hn : n ≤ s.length) : s.Pos where
--   offset := (s.data.take n).toByteString.utf8Size
--   validOffset := {
--     le_utf8Size := by
--       conv => rhs; rw [← toByteString_data (b := s)]
--       apply List.IsPrefix.utf8Size_toByteString_le
--       exact List.take_prefix n s.data
--     isValidUtf8 := by
--       simp only [numBytes_utf8Size, List.bytes_toByteString]
--       rw [ByteString.extract_bytes_of_isPrefix _ _ (List.take_prefix n s.data)]
--       exact isValidUtf8_utf8Encode
--   }


@[simp]
theorem ByteString.ByteOffset.numBytes_add {a b : ByteString.ByteOffset} :
    (a + b).numBytes = a.numBytes + b.numBytes := rfl

@[simp]
theorem ByteString.ByteOffset.numBytes_sub {a b : ByteString.ByteOffset} :
    (a - b).numBytes = a.numBytes - b.numBytes := rfl

@[simp]
theorem ByteString.utf8Size_append {s t : ByteString} : (s ++ t).utf8Size = s.utf8Size + t.utf8Size := by
  ext
  simp

theorem List.isPrefix_of_utf8Encode_append_eq_utf8Encode {l m : List Char} (b : ByteArray) (h : l.utf8Encode ++ b = m.utf8Encode) : l <+: m := by
  induction l generalizing m with
  | nil => simp
  | cons c l ih =>
    replace h := congrArg ByteArray.utf8Decode? h
    rw [utf8Decode?_utf8Encode] at h
    rw [← List.singleton_append, utf8Encode_append, ByteArray.append_assoc,
      ByteArray.utf8Decode?_utf8Encode_singleton_append] at h
    suffices ∃ m', m = [c] ++ m' ∧ l.utf8Encode ++ b = m'.utf8Encode by
      obtain ⟨m', rfl, hm'⟩ := this
      simpa using ih hm'
    have hx : (l.utf8Encode ++ b).utf8Decode?.isSome := by
      exact Option.isSome_map ▸ Option.isSome_of_eq_some h
    refine ⟨(l.utf8Encode ++ b).utf8Decode?.get hx |>.toList, ?_, by simp⟩
    exact List.toArray_inj (Option.some_inj.1 (by simp [← h]))

theorem ByteString.ValidOffset.exists {s : ByteString} {off : ByteOffset} (h : s.ValidOffset off) :
    ∃ m₁ m₂ : List Char, m₁.utf8Encode = s.bytes.extract 0 off.numBytes ∧ (m₁ ++ m₂).toByteString = s := by
  obtain ⟨⟨l, hl⟩⟩ := s.isValidUtf8
  obtain ⟨⟨m₁, hm₁⟩⟩ := h.isValidUtf8
  suffices m₁ <+: l by
    obtain ⟨m₂, rfl⟩ := this
    refine ⟨m₁, m₂, hm₁.symm, ?_⟩
    ext1
    simpa using hl.symm
  apply List.isPrefix_of_utf8Encode_append_eq_utf8Encode (s.bytes.extract off.numBytes s.bytes.size)
  rw [← hl, ← hm₁, ← ByteArray.extract_eq_extract_append_extract _ (by simp),
    ByteArray.extract_zero_size]
  simpa [ByteOffset.le_iff_numBytes_le] using h.le_utf8Size

theorem ByteString.ValidOffset.isValidUtf8' {s : ByteString} {off : ByteOffset} (h : s.ValidOffset off) :
    IsValidUtf8 (s.bytes.extract off.numBytes s.bytes.size) := by
  obtain ⟨m₁, m₂, hm, rfl⟩ := h.exists
  simp only [List.toByteString_append, bytes_append, List.bytes_toByteString]
  rw [ByteArray.extract_append_eq_right]
  · exact isValidUtf8_utf8Encode
  · rw [hm]
    simp only [List.toByteString_append, bytes_append, List.bytes_toByteString,
      ByteArray.size_extract, ByteArray.size_append, Nat.sub_zero]
    refine (Nat.min_eq_left ?_).symm
    simpa [ByteOffset.le_iff_numBytes_le] using h.le_utf8Size

theorem ByteString.isValidOffset_iff_exists_append {s : ByteString} {off : ByteOffset} :
    s.ValidOffset off ↔ ∃ s₁ s₂ : ByteString, s = s₁ ++ s₂ ∧ off = s₁.utf8Size := by
  refine ⟨fun h => ⟨⟨_, h.isValidUtf8⟩, ⟨_, h.isValidUtf8'⟩, ?_, ?_⟩, ?_⟩
  · ext1
    have := ByteString.ByteOffset.le_iff_numBytes_le.1 h.le_utf8Size
    simp_all
  · have := ByteString.ByteOffset.le_iff_numBytes_le.1 h.le_utf8Size
    simp_all [utf8Size]
  · rintro ⟨s₁, s₂, rfl, rfl⟩
    refine ⟨by simp [ByteOffset.le_iff_numBytes_le], ?_⟩
    simpa [ByteArray.extract_append_eq_left] using s₁.isValidUtf8

@[simp, grind]
theorem ByteString.validOffset_empty {offset : ByteOffset} :
    ByteString.empty.ValidOffset offset ↔ offset = 0 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨h₁, h₂⟩
    simp [ByteOffset.le_iff_numBytes_le] at h₁
    ext
    omega
  · rintro rfl
    simp

theorem List.validOffset_toByteString {l : List Char} {offset : ByteString.ByteOffset} :
    l.toByteString.ValidOffset offset ↔ ∃ i, offset = (l.take i).toByteString.utf8Size := by
  rw [ByteString.isValidOffset_iff_exists_append]
  refine ⟨?_, ?_⟩
  · rintro ⟨t₁, t₂, ht, rfl⟩
    refine ⟨t₁.length, ?_⟩
    have := congrArg ByteString.data ht
    simp only [data_toByteString, ByteString.data_append] at this
    subst this
    simp [← ByteString.size_toCharArray]
  · rintro ⟨i, rfl⟩
    refine ⟨(l.take i).toByteString, (l.drop i).toByteString, ?_, rfl⟩
    simp [← List.toByteString_append]

@[simp, grind]
theorem ByteString.validOffset_utf8size {s : ByteString} : s.ValidOffset s.utf8Size where
  le_utf8Size := Nat.le_refl _
  isValidUtf8 := by simp [s.isValidUtf8]

def UInt8.IsUtf8FirstByte (c : UInt8) : Prop :=
  c &&& 0x80 = 0 ∨ c &&& 0xe0 = 0xc0 ∨ c &&& 0xf0 = 0xe0 ∨ c &&& 0xf8 = 0xf0

@[inline]
def UInt8.isUtf8FirstByte (c : UInt8) : Bool :=
  c &&& 0x80 == 0 || c &&& 0xe0 == 0xc0 || c &&& 0xf0 = 0xe0 || c &&& 0xf8 == 0xf0

theorem UInt8.isUtf8FirstByte_eq_true {c : UInt8} :
    c.isUtf8FirstByte = true ↔ c.IsUtf8FirstByte := by
  grind [IsUtf8FirstByte, isUtf8FirstByte]

def ByteString.push (b : ByteString) (c : Char) : ByteString where
  bytes := b.bytes ++ [c].utf8Encode
  isValidUtf8 := by
    obtain ⟨l, rfl⟩ := b.exists_eq_toByteString
    rw [List.bytes_toByteString, ← List.utf8Encode_append]
    apply isValidUtf8_utf8Encode

@[simp]
theorem ByteString.bytes_push {s : ByteString} {c : Char} : (s.push c).bytes = s.bytes ++ [c].utf8Encode := rfl

theorem ByteString.ByteOffset.lt_iff_numBytes_lt {a b : ByteString.ByteOffset} :
    a < b ↔ a.numBytes < b.numBytes := Iff.rfl

def ByteString.utf8ByteAt (s : ByteString) (off : ByteString.ByteOffset) (h : off < s.utf8Size) : UInt8 :=
  s.bytes[off.numBytes]

def Char.utf8Size' (c : Char) : ByteString.ByteOffset :=
  ⟨c.utf8Size⟩

@[simp]
theorem Char.numBytes_utf8Size' {c : Char} : c.utf8Size'.numBytes = c.utf8Size := rfl

theorem Char.utf8Size'_pos {c : Char} : 0 < c.utf8Size' := by
  simp [ByteString.ByteOffset.lt_iff_numBytes_lt, Char.utf8Size_pos]

@[simp]
theorem ByteString.utf8Size_push {s : ByteString} {c : Char} : (s.push c).utf8Size = s.utf8Size + c.utf8Size' := by
  ext
  simp [List.utf8Encode_singleton]

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
theorem ByteString.utf8size_singleton {c : Char} : (ByteString.singleton c).utf8Size = c.utf8Size' := by
  ext
  simp [singleton]

theorem ByteString.singleton_eq_toByteString {c : Char} : ByteString.singleton c = [c].toByteString := by
  ext1
  simp

inductive IsGood (P : α → Prop) : List α → Prop where
  | intro {a : α} {as : List α} (ha : P a) (has : ∀ b ∈ as, ¬P b) : IsGood P (a::as)

theorem IsGood.getElem {P : α → Prop} {l : List α} (h : IsGood P l) (i : Nat) (hi : i < l.length) :
    P l[i] ↔ i = 0 := by
  cases h
  rename_i a as ha has
  rw [List.getElem_cons]
  split <;> simp_all

theorem BitVec.twoPow_le_of_getElem_eq_true {b : BitVec w} {i : Nat} {hi} (h : b[i]'hi = true) : twoPow w i ≤ b := by
  simp only [BitVec.le_def, BitVec.toNat_twoPow_of_lt hi]
  apply Nat.le_of_testBit
  simpa only [Nat.testBit_two_pow, decide_eq_true_eq, forall_eq', BitVec.testBit_toNat, BitVec.getLsbD_eq_getElem hi]

theorem BitVec.and_twoPow_eq_zero_of_lt {b : BitVec w} {i : Nat} (h : b < twoPow w i) : b &&& twoPow w i = 0#w := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  simp only [getElem_and, getElem_twoPow, getElem_zero, Bool.and_eq_false_imp,
    decide_eq_false_iff_not]
  rintro hbj rfl
  have := BitVec.twoPow_le_of_getElem_eq_true hbj
  simp only [BitVec.le_def, BitVec.lt_def] at h this
  omega

theorem isUtf8FirstByte_getElem_utf8EncodeChar (c : Char) (i : Nat) (hi : i < (String.utf8EncodeChar c).length) :
    UInt8.IsUtf8FirstByte ((String.utf8EncodeChar c)[i]'hi) ↔ i = 0 := by
  apply IsGood.getElem
  clear i hi
  fun_cases String.utf8EncodeChar c with
  | case1 v h =>
    subst v
    apply IsGood.intro
    · refine Or.inl ?_
      apply UInt8.eq_of_toBitVec_eq
      simp only [UInt8.toBitVec_and, UInt32.toBitVec_toUInt8, UInt8.toBitVec_ofNat]
      apply BitVec.and_twoPow_eq_zero_of_lt (i := 7)
      apply BitVec.lt_def.2
      simp only [UInt32.le_iff_toNat_le, UInt32.reduceToNat] at h
      simp only [BitVec.toNat_setWidth, UInt32.toNat_toBitVec, Nat.reducePow, BitVec.toNat_twoPow,
        Nat.reduceMod]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · simp
  | case2 v h₁ h₂ =>
    subst v
    apply IsGood.intro
    · refine Or.inr (Or.inl ?_)
      rw [UInt8.and_or_distrib_right, UInt8.and_assoc,
        (by decide : (31 : UInt8) &&& 224 = 0), UInt8.and_zero]
      decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
      rw [UInt8.IsUtf8FirstByte]
      simp only [UInt8.eq_iff_toBitVec_eq, UInt8.toBitVec_and, UInt8.toBitVec_or,
        UInt32.toBitVec_toUInt8, UInt8.toBitVec_ofNat, not_or]
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact mt (congrArg (·[7])) (by simp)
      · exact mt (congrArg (·[6])) (by simp)
      · exact mt (congrArg (·[6])) (by simp)
      · exact mt (congrArg (·[6])) (by simp)
  | case3 v h₁ h₂ h₃ =>
    subst v
    apply IsGood.intro
    · simp only [UInt8.IsUtf8FirstByte]
      refine Or.inr (Or.inr (Or.inl ?_))
      rw [UInt8.and_or_distrib_right, UInt8.and_assoc,
        (by decide : (15 : UInt8) &&& 240 = 0), UInt8.and_zero]
      decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      refine ⟨?_, ?_⟩
      all_goals
      · rw [UInt8.IsUtf8FirstByte]
        simp only [UInt8.eq_iff_toBitVec_eq, UInt8.toBitVec_and, UInt8.toBitVec_or,
          UInt32.toBitVec_toUInt8, UInt8.toBitVec_ofNat, not_or]
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact mt (congrArg (·[7])) (by simp)
        · exact mt (congrArg (·[6])) (by simp)
        · exact mt (congrArg (·[6])) (by simp)
        · exact mt (congrArg (·[6])) (by simp)
  | case4 v h₁ h₂ h₃ =>
    subst v
    apply IsGood.intro
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [UInt8.and_or_distrib_right, UInt8.and_assoc,
        (by decide : (7 : UInt8) &&& 248 = 0), UInt8.and_zero]
      decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      refine ⟨?_, ?_, ?_⟩
      all_goals
      · rw [UInt8.IsUtf8FirstByte]
        simp only [UInt8.eq_iff_toBitVec_eq, UInt8.toBitVec_and, UInt8.toBitVec_or,
          UInt32.toBitVec_toUInt8, UInt8.toBitVec_ofNat, not_or]
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact mt (congrArg (·[7])) (by simp)
        · exact mt (congrArg (·[6])) (by simp)
        · exact mt (congrArg (·[6])) (by simp)
        · exact mt (congrArg (·[6])) (by simp)

theorem isUtf8FirstByte_getElem_zero_utf8EncodeChar_append {c : Char} {b : ByteArray} :
    (((String.utf8EncodeChar c).toByteArray ++ b)[0]'(by simp; have := c.utf8Size_pos; omega)).IsUtf8FirstByte := by
  rw [ByteArray.getElem_append_left (by simp [c.utf8Size_pos]),
    List.getElem_toByteArray, isUtf8FirstByte_getElem_utf8EncodeChar]

theorem isUtf8FirstByte_getElem_zero_utf8EncodeChar {c : Char} :
    ((String.utf8EncodeChar c)[0]'(by simp [c.utf8Size_pos])).IsUtf8FirstByte := by
  simpa using isUtf8FirstByte_getElem_zero_utf8EncodeChar_append (b := .empty)

theorem isUtf8FirstByte_of_isSome_utf8DecodeChar? {b : ByteArray} {i : Nat}
    (h : (utf8DecodeChar? b i).isSome) : (b[i]'(lt_size_of_isSome_utf8DecodeChar? h)).IsUtf8FirstByte := by
  rw [utf8DecodeChar?_eq_utf8DecodeChar?_extract] at h
  suffices ((b.extract i b.size)[0]'(lt_size_of_isSome_utf8DecodeChar? h)).IsUtf8FirstByte by
    simpa [ByteArray.getElem_extract, Nat.add_zero] using this
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 h
  conv => congr; congr; rw [eq_of_utf8DecodeChar?_eq_some hc]
  exact isUtf8FirstByte_getElem_zero_utf8EncodeChar_append

theorem isUtf8FirstByte_getElem_utf8Encode_singleton {c : Char} {i : Nat} {hi : i < [c].utf8Encode.size} :
    UInt8.IsUtf8FirstByte [c].utf8Encode[i] ↔ i = 0 := by
  simp [List.utf8Encode_singleton, isUtf8FirstByte_getElem_utf8EncodeChar]

theorem ByteString.validOffset_singleton {c : Char} {off : ByteString.ByteOffset} :
    (ByteString.singleton c).ValidOffset off ↔ off = 0 ∨ off = c.utf8Size' := by
  rw [singleton_eq_toByteString, List.validOffset_toByteString]
  refine ⟨?_, ?_⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨rfl, hi⟩ : i = 0 ∨ 1 ≤ i := by omega
    · simp
    · rw [List.take_of_length_le (by simpa)]
      simp [← singleton_eq_toByteString]
  · rintro (rfl|rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp [← singleton_eq_toByteString]⟩

theorem ByteString.validOffset_singleton_utf8Size' {c : Char} :
    (ByteString.singleton c).ValidOffset c.utf8Size' :=
  validOffset_singleton.2 (Or.inr rfl)

@[simp]
theorem ByteString.append_singleton {s : ByteString} {c : Char} :
    s ++ ByteString.singleton c = s.push c := by
  ext1
  simp

theorem List.take_eq_take_min {l : List α} {i : Nat} : l.take i = l.take (min i l.length) := by
  simp [List.take_eq_take_iff]

theorem ByteString.validOffset_append {s t : ByteString} {off : ByteString.ByteOffset} :
    (s ++ t).ValidOffset off ↔ s.ValidOffset off ∨ (s.utf8Size ≤ off ∧ t.ValidOffset (off - s.utf8Size)) := by
  obtain ⟨s, rfl⟩ := exists_eq_toByteString s
  obtain ⟨t, rfl⟩ := exists_eq_toByteString t
  rw [← List.toByteString_append, List.validOffset_toByteString, List.validOffset_toByteString, List.validOffset_toByteString]
  refine ⟨?_, ?_⟩
  · rintro ⟨j, rfl⟩
    by_cases h : j ≤ s.length
    · exact Or.inl ⟨j, by simp [List.take_append_of_le_length h]⟩
    · refine Or.inr ⟨?_, ⟨j - s.length, ?_⟩⟩ <;>
        simp [List.take_append, List.take_of_length_le (i := j) (l := s) (by omega), ByteString.ByteOffset.le_iff_numBytes_le,
          ByteString.ByteOffset.ext_iff]
  · rintro (⟨j, rfl⟩|⟨h, ⟨j, hj⟩⟩)
    · refine ⟨min j s.length, ?_⟩
      rw [List.take_append_of_le_length (Nat.min_le_right ..), ← List.take_eq_take_min]
    · refine ⟨s.length + j, ?_⟩
      simp only [ByteOffset.ext_iff, ByteOffset.numBytes_sub, numBytes_utf8Size,
        List.bytes_toByteString, ByteOffset.le_iff_numBytes_le] at hj h
      simp [List.take_append, List.take_of_length_le (i := s.length + j) (l := s) (by omega), ByteString.ByteOffset.ext_iff]
      omega

theorem ByteString.ValidOffset.append_left {t : ByteString} {off : ByteString.ByteOffset} (h : t.ValidOffset off) (s : ByteString) :
    (s ++ t).ValidOffset (s.utf8Size + off) :=
  validOffset_append.2 (Or.inr ⟨by simp [ByteOffset.le_iff_numBytes_le], by
    suffices off = s.utf8Size + off - s.utf8Size by simp [← this, h]
    simp [ByteOffset.ext_iff]⟩)

theorem ByteString.ValidOffset.append_right {s : ByteString} {off : ByteString.ByteOffset} (h : s.ValidOffset off) (t : ByteString) :
    (s ++ t).ValidOffset off :=
  validOffset_append.2 (Or.inl h)

theorem ByteString.validOffset_push {s : ByteString} {c : Char} {off : ByteString.ByteOffset} :
    (s.push c).ValidOffset off ↔ s.ValidOffset off ∨ off = (s.push c).utf8Size := by
  rw [← append_singleton, validOffset_append, validOffset_singleton, utf8Size_append]
  simp [ByteString.ByteOffset.ext_iff, ByteString.ByteOffset.le_iff_numBytes_le, ByteString.ByteOffset.numBytes_sub]
  refine ⟨?_, ?_⟩
  · rintro (h|⟨h₁,(h₂|h₂)⟩)
    · grind
    · suffices off = s.utf8Size by grind
      simp [ByteString.ByteOffset.ext_iff]
      omega
    · grind
  · grind

theorem List.append_singleton_induction (l : List α) (motive : List α → Prop) (nil : motive [])
    (append_singleton : ∀ l a, motive l → motive (l ++ [a])) : motive l := by
  rw [← l.reverse_reverse]
  generalize l.reverse = m
  induction m with
  | nil => simpa
  | cons a m ih =>
    rw [reverse_cons]
    exact append_singleton _ _ ih

theorem ByteString.push_induction (s : ByteString) (motive : ByteString → Prop) (empty : motive ByteString.empty)
    (push : ∀ b c, motive b → motive (b.push c)) : motive s := by
  obtain ⟨m, rfl⟩ := s.exists_eq_toByteString
  apply List.append_singleton_induction m (motive ·.toByteString)
  · simpa
  · intro l c hl
    rw [List.toByteString_append, append_toByteString_singleton]
    exact push _ _ hl

theorem ByteString.validOffset_iff_isUtf8FirstByte (s : ByteString) (off : ByteString.ByteOffset) :
    s.ValidOffset off ↔
      (off = s.utf8Size ∨ (∃ (h : off < s.utf8Size), UInt8.IsUtf8FirstByte (s.utf8ByteAt off h))) := by
  induction s using ByteString.push_induction with
  | empty => simp [ByteString.ByteOffset.lt_iff_numBytes_lt]
  | push s c ih =>
    rw [validOffset_push, ih]
    refine ⟨?_, ?_⟩
    · rintro ((rfl|⟨h, hb⟩)|h)
      · refine Or.inr ⟨by simp [ByteString.ByteOffset.lt_iff_numBytes_lt, Char.utf8Size_pos], ?_⟩
        simp only [utf8ByteAt, bytes_push, numBytes_utf8Size]
        rw [ByteArray.getElem_append_right (Nat.le_refl _)]
        simp [isUtf8FirstByte_getElem_utf8Encode_singleton]
      · refine Or.inr ⟨by simp [ByteString.ByteOffset.lt_iff_numBytes_lt] at h; simp [ByteString.ByteOffset.lt_iff_numBytes_lt]; omega, ?_⟩
        simp only [utf8ByteAt, bytes_push]
        rwa [ByteArray.getElem_append_left, ← utf8ByteAt]
      · exact Or.inl h
    · rintro (h|⟨h, hb⟩)
      · exact Or.inr h
      · simp only [utf8ByteAt, bytes_push] at hb
        by_cases h' : off < s.utf8Size
        · refine Or.inl (Or.inr ⟨h', ?_⟩)
          rwa [ByteArray.getElem_append_left h', ← utf8ByteAt] at hb
        · refine Or.inl (Or.inl ?_)
          rw [ByteArray.getElem_append_right (by simp [ByteString.ByteOffset.lt_iff_numBytes_lt] at h'; omega)] at hb
          simp [isUtf8FirstByte_getElem_utf8Encode_singleton] at hb
          ext
          simp [ByteString.ByteOffset.lt_iff_numBytes_lt] at ⊢ h'
          omega

theorem ByteString.validOffset_iff_isSome_utf8DecodeChar? {s : ByteString} {off : ByteOffset} :
    s.ValidOffset off ↔ off = s.utf8Size ∨ (utf8DecodeChar? s.bytes off.numBytes).isSome := by
  refine ⟨?_, fun h => h.elim (by rintro rfl; simp) (fun h => ?_)⟩
  · induction s using ByteString.push_induction with
    | empty => simp [utf8DecodeChar?]
    | push s c ih =>
      simp only [validOffset_push, utf8Size_push, bytes_push]
      refine ?_ ∘ Or.imp_left ih
      rintro ((rfl|h)|rfl)
      · rw [utf8DecodeChar?_eq_utf8DecodeChar?_extract, ByteArray.extract_append_eq_right (by simp)]
        simp
      · exact Or.inr (isSome_utf8DecodeChar?_append h _)
      · simp
  · refine (ByteString.validOffset_iff_isUtf8FirstByte _ _).2 (Or.inr ?_)
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 h
    refine ⟨?_, ?_⟩
    · have := le_size_of_utf8DecodeChar?_eq_some hc
      have := c.utf8Size_pos
      simp only [ByteOffset.lt_iff_numBytes_lt, numBytes_utf8Size]
      omega
    · rw [utf8ByteAt]
      exact isUtf8FirstByte_of_isSome_utf8DecodeChar? h

deriving instance DecidableEq for ByteString.ByteOffset

theorem IsValidUtf8.isUtf8FirstByte_getElem_zero {b : ByteArray} (h : IsValidUtf8 b) (h₀ : 0 < b.size) :
    b[0].IsUtf8FirstByte := by
  rcases h with ⟨m, rfl⟩
  have : m ≠ [] := by
    rintro rfl
    simp at h₀
  conv => congr; congr; rw [← List.head_cons_tail this, ← List.singleton_append, List.utf8Encode_append]
  rw [ByteArray.getElem_append_left]
  -- https://github.com/leanprover/lean4/issues/10172
  · conv => congr; congr; rw [List.utf8Encode_singleton]
    rw [List.getElem_toByteArray]
    · rw [isUtf8FirstByte_getElem_utf8EncodeChar]
    · simp [List.utf8Encode_singleton, Char.utf8Size_pos]

theorem ByteString.isUtf8FirstByte_utf8ByteAt_zero {b : ByteString} {h} : (b.utf8ByteAt 0 h).IsUtf8FirstByte :=
  b.isValidUtf8.isUtf8FirstByte_getElem_zero _

theorem ByteString.ByteOffset.le_trans {a b c : ByteOffset} : a ≤ b → b ≤ c → a ≤ c := by
  simpa [ByteOffset.le_iff_numBytes_le] using Nat.le_trans

theorem ByteString.ByteOffset.lt_of_lt_of_le {a b c : ByteOffset} : a < b → b ≤ c → a < c := by
  simpa [ByteOffset.le_iff_numBytes_le, ByteOffset.lt_iff_numBytes_lt] using Nat.lt_of_lt_of_le

theorem ByteString.ByteOffset.isValidUtf8_extract_iff {s : ByteString} (off₁ off₂ : ByteString.ByteOffset) (hle : off₁ ≤ off₂) (hle' : off₂ ≤ s.utf8Size) :
    IsValidUtf8 (s.bytes.extract off₁.numBytes off₂.numBytes) ↔ off₁ = off₂ ∨ (s.ValidOffset off₁ ∧ s.ValidOffset off₂) := by
  have hle'' : off₂.numBytes ≤ s.bytes.size := by
    simpa [ByteOffset.le_iff_numBytes_le] using hle'
  refine ⟨fun h => Classical.or_iff_not_imp_left.2 (fun h' => ?_), ?_⟩
  · have hlt : off₁ < off₂ := by
      simp_all [ByteOffset.le_iff_numBytes_le, ByteOffset.lt_iff_numBytes_lt, ByteOffset.ext_iff]
      omega
    have h₁ : s.ValidOffset off₁ := by
      rw [ByteString.validOffset_iff_isUtf8FirstByte]
      refine Or.inr ⟨ByteOffset.lt_of_lt_of_le hlt hle', ?_⟩
      have hlt' : 0 < off₂.numBytes - off₁.numBytes := by
        simp [ByteOffset.lt_iff_numBytes_lt] at hlt
        omega
      have := h.isUtf8FirstByte_getElem_zero
      simp only [ByteArray.size_extract, Nat.min_eq_left hle'', hlt', ByteArray.getElem_extract, Nat.add_zero] at this
      simp [ByteString.utf8ByteAt, this trivial]
    refine ⟨h₁, ⟨hle', ?_⟩⟩
    rw [ByteArray.extract_eq_extract_append_extract off₁.numBytes (by simp) hle]
    exact h₁.isValidUtf8.append h
  · refine fun h => h.elim (by rintro rfl; simp) (fun ⟨h₁, h₂⟩ => ?_)
    let t : ByteString := ⟨_, h₂.isValidUtf8⟩
    have htb : t.bytes = s.bytes.extract 0 off₂.numBytes := rfl
    have ht : t.ValidOffset off₁ := by
      refine ⟨?_, ?_⟩
      · simpa [ByteOffset.le_iff_numBytes_le, t, Nat.min_eq_left hle'']
      · simpa [htb, ByteArray.extract_extract, Nat.min_eq_left (ByteOffset.le_iff_numBytes_le.1 hle)] using h₁.isValidUtf8
    simpa [htb, ByteArray.extract_extract, Nat.zero_add, Nat.min_eq_left hle''] using ht.isValidUtf8'

theorem ByteString.Pos.isValidUtf8_extract {s : ByteString} (pos₁ pos₂ : s.Pos) (h : pos₁.offset ≤ pos₂.offset) :
    IsValidUtf8 (s.bytes.extract pos₁.offset.numBytes pos₂.offset.numBytes) :=
  (ByteString.ByteOffset.isValidUtf8_extract_iff _ _ h pos₂.validOffset.le_utf8Size).2 (Or.inr ⟨pos₁.validOffset, pos₂.validOffset⟩)

structure ByteString.Slice.ValidOffset (s : ByteString.Slice) (off : ByteString.ByteOffset) : Prop where
  le_utf8Size : off ≤ s.utf8Size
  validOffset_add : s.str.ValidOffset (s.startInclusive.offset + off)

theorem ByteString.Slice.validOffset_iff_le_utf8Size_and_validOffset_add {s : ByteString.Slice} {off : ByteString.ByteOffset} :
    s.ValidOffset off ↔ off ≤ s.utf8Size ∧ s.str.ValidOffset (s.startInclusive.offset + off) :=
  ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

@[ext]
structure ByteString.Slice.Pos (s : ByteString.Slice) where
  offset : ByteOffset
  validOffset : s.ValidOffset offset
deriving DecidableEq

@[simp]
theorem ByteString.Slice.numBytes_utf8Size {s : ByteString.Slice} : s.utf8Size.numBytes = s.endExclusive.offset.numBytes - s.startInclusive.offset.numBytes := by
  simp [utf8Size]

def ByteString.Slice.utf8ByteAt (s : ByteString.Slice) (off : ByteString.ByteOffset) (h : off < s.utf8Size) : UInt8 :=
  s.str.utf8ByteAt (s.startInclusive.offset + off) (by
    -- TODO: probably there is some lemma to extract here
    have := s.endExclusive.validOffset.1
    simp [ByteString.ByteOffset.lt_iff_numBytes_lt, ByteString.ByteOffset.le_iff_numBytes_le] at *
    omega)

def ByteString.Slice.copy (s : ByteString.Slice) : ByteString where
  bytes := s.str.bytes.extract s.startInclusive.offset.numBytes s.endExclusive.offset.numBytes
  isValidUtf8 := s.startInclusive.isValidUtf8_extract s.endExclusive s.startInclusive_le_endExclusive

theorem ByteString.Slice.bytes_copy {s : ByteString.Slice} :
    s.copy.bytes = s.str.bytes.extract s.startInclusive.offset.numBytes s.endExclusive.offset.numBytes := rfl

@[simp]
theorem ByteString.Slice.utf8Size_copy {s : ByteString.Slice} : s.copy.utf8Size = s.utf8Size := by
  ext
  simp only [copy, ByteString.numBytes_utf8Size, ByteArray.size_extract, numBytes_utf8Size]
  rw [Nat.min_eq_left (by simpa [ByteOffset.le_iff_numBytes_le] using s.endExclusive.validOffset.le_utf8Size)]

@[simp]
theorem ByteString.Slice.size_bytes_copy {s : ByteString.Slice} :
    s.copy.bytes.size = s.endExclusive.offset.numBytes - s.startInclusive.offset.numBytes := by
  rw [← numBytes_utf8Size, ← ByteString.numBytes_utf8Size, utf8Size_copy]

theorem ByteString.Slice.utf8ByteAt_eq_utf8ByteAt_copy {s : ByteString.Slice} {off : ByteString.ByteOffset} {h : off < s.utf8Size} :
    s.utf8ByteAt off h = s.copy.utf8ByteAt off (by simpa) := by
  simp [utf8ByteAt, copy, ByteString.utf8ByteAt, ByteArray.getElem_extract]

theorem ByteString.Slice.utf8ByteAt_copy {s : ByteString.Slice} {off : ByteString.ByteOffset} {h} :
    s.copy.utf8ByteAt off h = s.utf8ByteAt off (by simpa using h) := by
  rw [ByteString.Slice.utf8ByteAt_eq_utf8ByteAt_copy]

theorem ByteString.Slice.isUtf8FirstByte_utf8ByteAt_zero {s : ByteString.Slice} (h : 0 < s.utf8Size) :
    (s.utf8ByteAt 0 h).IsUtf8FirstByte := by
  simpa [utf8ByteAt_eq_utf8ByteAt_copy] using s.copy.isUtf8FirstByte_utf8ByteAt_zero

@[simp]
theorem ByteString.ByteOffset.add_zero {b : ByteString.ByteOffset} : b + 0 = b := by
  simp [ByteOffset.ext_iff]

@[simp]
theorem ByteString.Slice.validOffset_copy_iff {s : ByteString.Slice} {off : ByteOffset} :
    s.copy.ValidOffset off ↔ s.ValidOffset off := by
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨?_, ?_⟩, fun ⟨h₁, h₂⟩ => ⟨?_, ?_⟩⟩
  · simpa using h₁
  · have := s.startInclusive_le_endExclusive
    simp_all [ByteOffset.le_iff_numBytes_le]
    rw [bytes_copy, ByteArray.extract_extract, Nat.add_zero, Nat.min_eq_left (by omega)] at h₂
    rw [← ByteOffset.numBytes_add, ByteString.ByteOffset.isValidUtf8_extract_iff] at h₂
    · rcases h₂ with (h₂|⟨-, h₂⟩)
      · rw [← h₂]
        exact s.startInclusive.validOffset
      · exact h₂
    · simp [ByteOffset.le_iff_numBytes_le]
    · have := s.endExclusive.validOffset.le_utf8Size
      simp_all [ByteOffset.le_iff_numBytes_le]
      omega
  · simpa using h₁
  · have := s.startInclusive_le_endExclusive
    simp_all [ByteOffset.le_iff_numBytes_le]
    rw [bytes_copy, ByteArray.extract_extract, Nat.add_zero, Nat.min_eq_left (by omega)]
    rw [← ByteOffset.numBytes_add, ByteString.ByteOffset.isValidUtf8_extract_iff]
    · exact Or.inr ⟨s.startInclusive.validOffset, h₂⟩
    · simp [ByteOffset.le_iff_numBytes_le]
    · have := s.endExclusive.validOffset.le_utf8Size
      simp_all [ByteOffset.le_iff_numBytes_le]
      omega

def ByteString.Slice.startPos (s : ByteString.Slice) : s.Pos where
  offset := 0
  validOffset := ⟨by simp [ByteOffset.le_iff_numBytes_le], by simpa using s.startInclusive.validOffset⟩

@[simp]
theorem ByteString.Slice.offset_startPos {s : ByteString.Slice} : s.startPos.offset = 0 := rfl

instance {s : ByteString.Slice} : Inhabited s.Pos where
  default := s.startPos

@[simp]
theorem ByteString.Slice.offset_startInclusive_add_utf8Size {s : ByteString.Slice} :
    s.startInclusive.offset + s.utf8Size = s.endExclusive.offset := by
  have := s.startInclusive_le_endExclusive
  simp_all [ByteOffset.ext_iff, ByteOffset.le_iff_numBytes_le]

def ByteString.Slice.endPos (s : ByteString.Slice) : s.Pos where
  offset := s.utf8Size
  validOffset := ⟨by simp [ByteOffset.le_iff_numBytes_le], by simpa using s.endExclusive.validOffset⟩

@[simp]
theorem ByteString.Slice.offset_endPos {s : ByteString.Slice} : s.endPos.offset = s.utf8Size := rfl

theorem ByteString.Slice.validOffset_iff_isUtf8FirstByte (s : ByteString.Slice) (off : ByteString.ByteOffset) :
    s.ValidOffset off ↔ (off = s.utf8Size ∨ (∃ (h : off < s.utf8Size), UInt8.IsUtf8FirstByte (s.utf8ByteAt off h))) := by
  simp only [← validOffset_copy_iff, ByteString.validOffset_iff_isUtf8FirstByte, utf8Size_copy,
    utf8ByteAt_copy]

theorem ByteString.Slice.validOffset_iff_isSome_utf8DecodeChar?_copy (s : ByteString.Slice) (off : ByteOffset) :
    s.ValidOffset off ↔ off = s.utf8Size ∨ (utf8DecodeChar? s.copy.bytes off.numBytes).isSome := by
  rw [← validOffset_copy_iff, ByteString.validOffset_iff_isSome_utf8DecodeChar?, utf8Size_copy]

theorem ByteString.Slice.bytes_str_eq {s : ByteString.Slice} :
    s.str.bytes = s.str.bytes.extract 0 s.startInclusive.offset.numBytes ++
      s.copy.bytes ++ s.str.bytes.extract s.endExclusive.offset.numBytes s.str.bytes.size := by
  rw [bytes_copy, ← ByteArray.extract_eq_extract_append_extract, ← ByteArray.extract_eq_extract_append_extract,
    ByteArray.extract_zero_size]
  · simp
  · simpa [ByteOffset.le_iff_numBytes_le] using s.endExclusive.validOffset.le_utf8Size
  · simp
  · simpa [ByteOffset.le_iff_numBytes_le] using s.startInclusive_le_endExclusive

theorem ByteString.Slice.validOffset_iff_isSome_utf8DecodeChar? (s : ByteString.Slice) (off : ByteOffset) :
    s.ValidOffset off ↔ off = s.utf8Size ∨ (off < s.utf8Size ∧ (utf8DecodeChar? s.str.bytes (s.startInclusive.offset.numBytes + off.numBytes)).isSome) := by
  refine ⟨?_, ?_⟩
  · rw [ByteString.Slice.validOffset_iff_isSome_utf8DecodeChar?_copy]
    rintro (rfl|h)
    · simp
    · refine Or.inr ⟨?_, ?_⟩
      · have := lt_size_of_isSome_utf8DecodeChar? h
        simpa [ByteOffset.lt_iff_numBytes_lt] using this
      · rw [utf8DecodeChar?_eq_utf8DecodeChar?_extract] at h
        rw [bytes_str_eq, ByteArray.append_assoc, utf8DecodeChar?_eq_utf8DecodeChar?_extract]
        simp only [ByteArray.size_append, ByteArray.size_extract, Nat.sub_zero, Nat.le_refl,
          Nat.min_eq_left]
        have h' : s.startInclusive.offset.numBytes ≤ s.str.bytes.size := by
          simpa [ByteOffset.le_iff_numBytes_le] using s.startInclusive.validOffset.le_utf8Size
        rw [Nat.min_eq_left h', ByteArray.extract_append_size_add' (by simp [h']),
          ByteArray.extract_append, Nat.add_sub_cancel_left]
        rw [ByteArray.extract_eq_extract_append_extract s.copy.bytes.size]
        · rw [ByteArray.append_assoc]
          apply isSome_utf8DecodeChar?_append h
        · have := lt_size_of_isSome_utf8DecodeChar? h
          simp only [size_bytes_copy, ByteArray.size_extract, Nat.le_refl, Nat.min_eq_left] at this
          simp only [size_bytes_copy, ge_iff_le]
          omega
        · simp
  · rw [ByteString.Slice.validOffset_iff_isUtf8FirstByte]
    rintro (rfl|⟨h₁, h₂⟩)
    · simp
    · exact Or.inr ⟨h₁, isUtf8FirstByte_of_isSome_utf8DecodeChar? h₂⟩

@[inline]
def ByteString.Slice.isValidOffset (s : ByteString.Slice) (off : ByteString.ByteOffset) : Bool :=
  if off = s.utf8Size then
    true
  else if h : off < s.utf8Size then
    (s.utf8ByteAt off h).isUtf8FirstByte
  else
    false

theorem ByteString.Slice.isValidOffset_eq_true {s : ByteString.Slice} {off : ByteString.ByteOffset} :
    s.isValidOffset off = true ↔ s.ValidOffset off := by
  fun_cases ByteString.Slice.isValidOffset with grind [UInt8.isUtf8FirstByte_eq_true, ByteString.Slice.validOffset_iff_isUtf8FirstByte]

def ByteString.Slice.Pos.byte {s : ByteString.Slice} (pos : s.Pos) (h : pos ≠ s.endPos) : UInt8 :=
  s.utf8ByteAt pos.offset (by
    have := pos.validOffset.le_utf8Size
    simp_all [Pos.ext_iff, ByteOffset.ext_iff, ByteOffset.le_iff_numBytes_le, ByteOffset.lt_iff_numBytes_lt]
    omega)

theorem ByteString.Slice.Pos.isUtf8FirstByte_byte {s : ByteString.Slice} {pos : s.Pos} {h : pos ≠ s.endPos} :
    (pos.byte h).IsUtf8FirstByte :=
  ((s.validOffset_iff_isUtf8FirstByte pos.offset |>.1 pos.validOffset).elim (fun h' => (h (Pos.ext h')).elim) (·.2))

-- For testing/debugging
def String.toByteString (s : String) : ByteString :=
  s.data.toByteString

-- For testing/debugging
def ByteString.toString (s : ByteString) : String :=
  ⟨s.data⟩

def ByteString.Slice.Pos.up {s : ByteString.Slice} (pos : s.Pos) : s.str.Pos where
  offset := s.startInclusive.offset + pos.offset
  validOffset := pos.validOffset.validOffset_add

@[simp]
theorem ByteString.Slice.Pos.offset_up {s : ByteString.Slice} {pos : s.Pos} :
    pos.up.offset = s.startInclusive.offset + pos.offset := rfl

@[simp]
theorem ByteString.Slice.Pos.offset_up_le_offset_endExclusive {s : ByteString.Slice} {pos : s.Pos} :
    pos.up.offset ≤ s.endExclusive.offset := by
  have := pos.validOffset.le_utf8Size
  have := s.startInclusive_le_endExclusive
  simp only [ByteOffset.le_iff_numBytes_le, numBytes_utf8Size, Pos.offset_up,
    ByteOffset.numBytes_add, ge_iff_le] at *
  omega

theorem ByteString.Slice.Pos.offset_le_offset_up {s : ByteString.Slice} {pos : s.Pos} :
    pos.offset ≤ pos.up.offset := by
  simp [ByteOffset.le_iff_numBytes_le]

@[simp]
theorem ByteString.Slice.Pos.offset_le_offset_endExclusive {s : ByteString.Slice} {pos : s.Pos} :
    pos.offset ≤ s.endExclusive.offset :=
  ByteOffset.le_trans offset_le_offset_up offset_up_le_offset_endExclusive

def ByteString.Slice.replaceStart (s : ByteString.Slice) (pos : s.Pos) : ByteString.Slice where
  str := s.str
  startInclusive := pos.up
  endExclusive := s.endExclusive
  startInclusive_le_endExclusive := Pos.offset_up_le_offset_endExclusive

@[simp]
theorem ByteString.Slice.str_replaceStart {s : ByteString.Slice} {pos : s.Pos} :
    (s.replaceStart pos).str = s.str := rfl

@[simp]
theorem ByteString.Slice.startInclusive_replaceStart {s : ByteString.Slice} {pos : s.Pos} :
    (s.replaceStart pos).startInclusive = pos.up := rfl

@[simp]
theorem ByteString.Slice.endExclusive_replaceStart {s : ByteString.Slice} {pos : s.Pos} :
    (s.replaceStart pos).endExclusive = s.endExclusive := rfl

def ByteString.Slice.replaceEnd (s : ByteString.Slice) (pos : s.Pos) : ByteString.Slice where
  str := s.str
  startInclusive := s.startInclusive
  endExclusive := pos.up
  startInclusive_le_endExclusive := by simp [ByteOffset.le_iff_numBytes_le]

@[simp]
theorem ByteString.Slice.str_replaceEnd {s : ByteString.Slice} {pos : s.Pos} :
    (s.replaceEnd pos).str = s.str := rfl

@[simp]
theorem ByteString.Slice.startInclusive_replaceEnd {s : ByteString.Slice} {pos : s.Pos} :
    (s.replaceEnd pos).startInclusive = s.startInclusive := rfl

@[simp]
theorem ByteString.Slice.endExclusive_replaceEnd {s : ByteString.Slice} {pos : s.Pos} :
    (s.replaceEnd pos).endExclusive = pos.up := rfl

@[simp]
theorem ByteString.Slice.utf8Size_replaceStart {s : ByteString.Slice} {pos : s.Pos} :
    (s.replaceStart pos).utf8Size = s.utf8Size - pos.offset := by
  ext
  simp
  omega

@[simp]
theorem ByteString.Slice.utf8Size_replaceEnd {s : ByteString.Slice} {pos : s.Pos} :
    (s.replaceEnd pos).utf8Size = pos.offset := by
  ext
  simp

theorem ByteString.ByteOffset.add_comm (a b : ByteString.ByteOffset) : a + b = b + a := by
  ext
  simpa using Nat.add_comm _ _

theorem ByteString.ByteOffset.add_assoc (a b c : ByteString.ByteOffset) : a + b + c = a + (b + c) := by
  ext
  simpa using Nat.add_assoc _ _ _

theorem ByteString.Slice.validOffset_replaceStart {s : ByteString.Slice} {pos : s.Pos} {off : ByteOffset} :
    (s.replaceStart pos).ValidOffset off ↔ s.ValidOffset (pos.offset + off) := by
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨?_, ?_⟩, fun ⟨h₁, h₂⟩ => ⟨?_, ?_⟩⟩
  · have := pos.validOffset.le_utf8Size
    simp_all [ByteOffset.le_iff_numBytes_le]
    omega
  · simp only [str_replaceStart, startInclusive_replaceStart, Pos.offset_up] at h₂
    rwa [← ByteOffset.add_assoc]
  · simp_all [ByteOffset.le_iff_numBytes_le]
    omega
  · simp only [str_replaceStart, startInclusive_replaceStart, Pos.offset_up]
    rwa [ByteOffset.add_assoc]

theorem ByteString.Slice.validOffset_replaceEnd {s : ByteString.Slice} {pos : s.Pos} {off : ByteOffset} :
    (s.replaceEnd pos).ValidOffset off ↔ off ≤ pos.offset ∧ s.ValidOffset off := by
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨?_, ?_, ?_⟩, fun ⟨h₁, ⟨h₂, h₃⟩⟩ => ⟨?_, ?_⟩⟩
  · simpa using h₁
  · simp only [utf8Size_replaceEnd] at h₁
    exact ByteOffset.le_trans h₁ pos.validOffset.le_utf8Size
  · simpa using h₂
  · simpa using h₁
  · simpa using h₃

def ByteString.Slice.Pos.get {s : ByteString.Slice} (pos : s.Pos) (h : pos ≠ s.endPos) : Char :=
  utf8DecodeChar s.str.bytes (s.startInclusive.offset.numBytes + pos.offset.numBytes)
    (((Slice.validOffset_iff_isSome_utf8DecodeChar? _ _).1 pos.validOffset).elim (by simp_all [Pos.ext_iff]) (·.2))

def ByteString.Slice.Pos.get? {s : ByteString.Slice} (pos : s.Pos) : Option Char :=
  if h : pos = s.endPos then none else some (pos.get h)

def ByteString.Slice.Pos.get! {s : ByteString.Slice} (pos : s.Pos) : Char :=
  if h : pos = s.endPos then panic! "Cannot retrieve character at end position" else pos.get h

@[simp]
theorem ByteString.startInclusive_toSlice {s : ByteString} : s.toSlice.startInclusive = s.startPos := rfl

@[simp]
theorem ByteString.endExclusive_toSlice {s : ByteString} : s.toSlice.endExclusive = s.endPos := rfl

@[simp]
theorem ByteString.str_toSlice {s : ByteString} : s.toSlice.str = s := rfl

@[simp]
theorem ByteString.offset_startPos {s : ByteString} : s.startPos.offset = 0 := rfl

@[simp]
theorem ByteString.offset_endPos {s : ByteString} : s.endPos.offset = s.utf8Size := rfl

@[simp]
theorem ByteString.copy_toSlice {s : ByteString} : s.toSlice.copy = s := by
  ext1
  simp [Slice.bytes_copy]

@[simp]
theorem ByteString.validOffset_toSlice_iff {s : ByteString} {off : ByteOffset} :
    s.toSlice.ValidOffset off ↔ s.ValidOffset off := by
  rw [← Slice.validOffset_copy_iff, copy_toSlice]

theorem ByteString.ValidOffset.toSlice {s : ByteString} {off : ByteOffset} (h : s.ValidOffset off) :
    s.toSlice.ValidOffset off :=
  validOffset_toSlice_iff.2 h

theorem ByteString.Slice.ValidOffset.ofSlice {s : ByteString} {off : ByteOffset} (h : s.toSlice.ValidOffset off) :
    s.ValidOffset off :=
  validOffset_toSlice_iff.1 h

@[inline]
def ByteString.Pos.toSlice {s : ByteString} (pos : s.Pos) : s.toSlice.Pos where
  offset := pos.offset
  validOffset := pos.validOffset.toSlice

@[simp]
theorem ByteString.Pos.offset_toSlice {s : ByteString} {pos : s.Pos} : pos.toSlice.offset = pos.offset := rfl

@[inline]
def ByteString.Slice.Pos.ofSlice {s : ByteString} (pos : s.toSlice.Pos) : s.Pos where
  offset := pos.offset
  validOffset := pos.validOffset.ofSlice

@[simp]
theorem ByteString.Pos.ofset_offSlice {s : ByteString} {pos : s.toSlice.Pos} : pos.ofSlice.offset = pos.offset := rfl

@[simp]
theorem ByteString.utf8Size_toSlice {s : ByteString} : s.toSlice.utf8Size = s.utf8Size := by
  rw [← Slice.utf8Size_copy, copy_toSlice]

@[simp]
theorem ByteString.toSlice_endPos {s : ByteString} : s.toSlice.endPos = s.endPos.toSlice :=
  ByteString.Slice.Pos.ext (by simp)

attribute [ext] ByteString.Pos

@[simp]
theorem ByteString.Pos.ofSlice_toSlice {s : ByteString} (pos : s.Pos) : pos.toSlice.ofSlice = pos :=
  ByteString.Pos.ext (by simp)

@[simp]
theorem ByteString.Pos.Slice.toSlice_ofSlice {s : ByteString} (pos : s.toSlice.Pos) : pos.ofSlice.toSlice = pos :=
  ByteString.Slice.Pos.ext (by simp)

def ByteString.Pos.get {s : ByteString} (pos : s.Pos) (h : pos ≠ s.endPos) : Char :=
  pos.toSlice.get (ne_of_apply_ne Slice.Pos.ofSlice (by simp [h]))

def ByteString.Pos.get? {s : ByteString} (pos : s.Pos) : Option Char :=
  pos.toSlice.get?

def ByteString.Pos.get! {s : ByteString} (pos : s.Pos) : Char :=
  pos.toSlice.get!

def ByteString.Pos.byte {s : ByteString} (pos : s.Pos) (h : pos ≠ s.endPos) : UInt8 :=
  pos.toSlice.byte (ne_of_apply_ne Slice.Pos.ofSlice (by simp [h]))

theorem ByteString.append_left_inj {s₁ s₂ : ByteString} (t : ByteString) :
    s₁ ++ t = s₂ ++ t ↔ s₁ = s₂ := by
  simp [← ByteString.data_inj]

theorem ByteString.append_assoc {s₁ s₂ s₃ : ByteString} : s₁ ++ s₂ ++ s₃ = s₁ ++ (s₂ ++ s₃) := by
  simp [← ByteString.data_inj]

@[simp]
theorem ByteString.startPos_eq_endPos_iff {b : ByteString} : b.startPos = b.endPos ↔ b = empty := by
  rw [← utf8Size_eq_zero_iff, Pos.ext_iff, offset_startPos, offset_endPos, eq_comm]

@[simp]
theorem ByteString.data_eq_nil_iff {b : ByteString} : b.data = [] ↔ b = empty := by
  rw [← List.toByteString_inj, toByteString_data, List.toByteString_nil]

@[simp]
theorem List.toByteString_eq_empty_iff {l : List Char} : l.toByteString = ByteString.empty ↔ l = [] := by
  rw [← ByteString.data_inj, data_toByteString, ByteString.data_empty]

@[simp]
theorem List.length_toByteString {l : List Char} : l.toByteString.length = l.length := by
  rw [← ByteString.length_data, data_toByteString]

theorem ByteString.isSome_utf8DecodeChar?_zero {b : ByteString} (hb : b ≠ empty) : (utf8DecodeChar? b.bytes 0).isSome := by
  refine (((validOffset_iff_isSome_utf8DecodeChar? (s := b)).1 validOffset_zero).elim ?_ id)
  rw [eq_comm, utf8Size_eq_zero_iff]
  exact fun h => (hb h).elim

theorem ByteString.head_data {b : ByteString} {h} :
    b.data.head h = utf8DecodeChar b.bytes 0 (isSome_utf8DecodeChar?_zero (by simpa using h)) := by
  obtain ⟨l, rfl⟩ := b.exists_eq_toByteString
  match l with
  | [] => simp at h
  | c::cs => simp

theorem ByteString.get_startPos {b : ByteString} (h) :
    b.startPos.get h = b.data.head (by rwa [ne_eq, data_eq_nil_iff, ← startPos_eq_endPos_iff]) :=
  head_data.symm

theorem ByteString.eq_singleton_append {s : ByteString} (h : s.startPos ≠ s.endPos) :
    ∃ t, s = singleton (s.startPos.get h) ++ t := by
  obtain ⟨m, rfl⟩ := s.exists_eq_toByteString
  have hm : m ≠ [] := by
    rwa [ne_eq, ← List.toByteString_eq_empty_iff, ← ByteString.startPos_eq_endPos_iff]
  refine ⟨m.tail.toByteString, ?_⟩
  rw (occs := [1]) [← List.head_cons_tail hm]
  rw [← List.singleton_append, List.toByteString_append, append_left_inj, ← singleton_eq_toByteString,
    get_startPos]
  simp

theorem ByteString.Slice.copy_eq_copy_replaceEnd {s : ByteString.Slice} {pos : s.Pos} :
    s.copy = (s.replaceEnd pos).copy ++ (s.replaceStart pos).copy := by
  rw [ByteString.ext_iff, bytes_copy, bytes_append, bytes_copy, bytes_copy]
  simp only [str_replaceEnd, startInclusive_replaceEnd, endExclusive_replaceEnd,
    Pos.offset_up, ByteOffset.numBytes_add, str_replaceStart, startInclusive_replaceStart,
    endExclusive_replaceStart, ByteArray.extract_append_extract, Nat.le_add_right, Nat.min_eq_left]
  rw [Nat.max_eq_right]
  exact pos.offset_up_le_offset_endExclusive

def ByteString.Pos.ofCopy {s : ByteString.Slice} (pos : s.copy.Pos) : s.Pos where
  offset := pos.offset
  validOffset := Slice.validOffset_copy_iff.1 pos.validOffset

@[simp]
theorem ByteString.Pos.offset_ofCopy {s : ByteString.Slice} {pos : s.copy.Pos} : pos.ofCopy.offset = pos.offset := rfl

def ByteString.Slice.Pos.toCopy {s : ByteString.Slice} (pos : s.Pos) : s.copy.Pos where
  offset := pos.offset
  validOffset := Slice.validOffset_copy_iff.2 pos.validOffset

@[simp]
theorem ByteString.Slice.Pos.offset_toCopy {s : ByteString.Slice} {pos : s.Pos} : pos.toCopy.offset = pos.offset := rfl

@[simp]
theorem ByteString.Slice.Pos.ofCopy_toCopy {s : ByteString.Slice} {pos : s.Pos} : pos.toCopy.ofCopy = pos :=
  ByteString.Slice.Pos.ext (by simp)

@[simp]
theorem ByteString.Pos.toCopy_ofCopy {s : ByteString.Slice} {pos : s.copy.Pos} : pos.ofCopy.toCopy = pos :=
  ByteString.Pos.ext (by simp)

theorem ByteString.Pos.ofCopy_inj {s : ByteString.Slice} {pos pos' : s.copy.Pos} : pos.ofCopy = pos'.ofCopy ↔ pos = pos' :=
  ⟨fun h => by simpa using congrArg Slice.Pos.toCopy h, (· ▸ rfl)⟩

@[simp]
theorem ByteString.Slice.startPos_copy {s : ByteString.Slice} : s.copy.startPos = s.startPos.toCopy :=
  ByteString.Pos.ext (by simp)

@[simp]
theorem ByteString.Slice.endPos_copy {s : ByteString.Slice} : s.copy.endPos = s.endPos.toCopy :=
  ByteString.Pos.ext (by simp)

theorem ByteString.Slice.Pos.get_toCopy {s : ByteString.Slice} {pos : s.Pos} (h) :
    pos.toCopy.get h = pos.get (by rintro rfl; simp at h) := by
  rw [ByteString.Pos.get, ByteString.Slice.Pos.get, ByteString.Slice.Pos.get]
  simp only [str_toSlice, bytes_copy, startInclusive_toSlice, startPos_copy, offset_toCopy,
    offset_startPos, ByteOffset.numBytes_zero, Pos.offset_toSlice, Nat.zero_add]
  rw [utf8DecodeChar_eq_utf8DecodeChar_extract]
  conv => lhs; congr; rw [ByteArray.extract_extract]
  conv => rhs; rw [utf8DecodeChar_eq_utf8DecodeChar_extract]
  exact utf8DecodeChar_extract_congr _ _ _

theorem ByteString.Slice.Pos.get_eq_get_toCopy {s : ByteString.Slice} {pos : s.Pos} {h} :
    pos.get h = pos.toCopy.get (ne_of_apply_ne Pos.ofCopy (by simp [h])) :=
  (get_toCopy _).symm

theorem ByteString.Slice.Pos.byte_toCopy {s : ByteString.Slice} {pos : s.Pos} (h) :
    pos.toCopy.byte h = pos.byte (by rintro rfl; simp at h) := by
  rw [ByteString.Pos.byte, ByteString.Slice.Pos.byte, ByteString.Slice.Pos.byte]
  simp [utf8ByteAt, ByteString.utf8ByteAt, bytes_copy, ByteArray.getElem_extract]

theorem ByteString.Slice.Pos.byte_eq_byte_toCopy {s : ByteString.Slice} {pos : s.Pos} {h} :
    pos.byte h = pos.toCopy.byte (ne_of_apply_ne Pos.ofCopy (by simp [h])) :=
  (byte_toCopy _).symm

def ByteString.Slice.Pos.ofReplaceStart {s : ByteString.Slice} {p₀ : s.Pos} (pos : (s.replaceStart p₀).Pos) : s.Pos where
  offset := p₀.offset + pos.offset
  validOffset := validOffset_replaceStart.1 pos.validOffset

@[simp]
theorem ByteString.Slice.Pos.offset_ofReplaceStart {s : ByteString.Slice} {p₀ : s.Pos} {pos : (s.replaceStart p₀).Pos} :
    (ofReplaceStart pos).offset = p₀.offset + pos.offset := rfl

def ByteString.Slice.Pos.toReplaceStart {s : ByteString.Slice} (p₀ : s.Pos) (pos : s.Pos) (h : p₀.offset ≤ pos.offset) :
    (s.replaceStart p₀).Pos where
  offset := pos.offset - p₀.offset
  validOffset := validOffset_replaceStart.2 (by
    have : p₀.offset + (pos.offset - p₀.offset) = pos.offset := by
      simp_all [ByteOffset.le_iff_numBytes_le, ByteOffset.ext_iff]
    simpa [this] using pos.validOffset)

@[simp]
theorem ByteString.Slice.Pos.offset_toReplaceStart {s : ByteString.Slice} {p₀ : s.Pos} {pos : s.Pos} {h} :
    (toReplaceStart p₀ pos h).offset = pos.offset - p₀.offset := rfl

@[simp]
theorem ByteString.Slice.Pos.ofReplaceStart_startPos {s : ByteString.Slice} {pos : s.Pos} :
    ofReplaceStart (s.replaceStart pos).startPos = pos :=
  ByteString.Slice.Pos.ext (by simp)

@[simp]
theorem ByteString.Slice.Pos.ofReplaceStart_endPos {s : ByteString.Slice} {pos : s.Pos} :
    ofReplaceStart (s.replaceStart pos).endPos = s.endPos := by
  have := pos.validOffset.le_utf8Size
  simp_all [Pos.ext_iff, ByteOffset.ext_iff, ByteOffset.le_iff_numBytes_le]

theorem ByteString.Slice.Pos.ofReplaceStart_inj {s : ByteString.Slice} {p₀ : s.Pos} {pos pos' : (s.replaceStart p₀).Pos} :
    ofReplaceStart pos = ofReplaceStart pos' ↔ pos = pos' := by
  simp [Pos.ext_iff, ByteOffset.ext_iff]

theorem ByteString.Slice.Pos.get_eq_get_ofReplaceStart {s : ByteString.Slice} {p₀ : s.Pos} {pos : (s.replaceStart p₀).Pos} {h} :
    pos.get h = (ofReplaceStart pos).get (by rwa [← ofReplaceStart_endPos, ne_eq, ofReplaceStart_inj]) := by
  simp [Slice.Pos.get, Nat.add_assoc]

theorem ByteString.Slice.Pos.copy_eq_append_get {s : ByteString.Slice} {pos : s.Pos} (h : pos ≠ s.endPos) :
    ∃ t₁ t₂ : ByteString, s.copy = t₁ ++ ByteString.singleton (pos.get h) ++ t₂ ∧ t₁.utf8Size = pos.offset := by
  obtain ⟨t₂, ht₂⟩ := (s.replaceStart pos).copy.eq_singleton_append (by simpa [← Pos.ofCopy_inj, ← ofReplaceStart_inj])
  refine ⟨(s.replaceEnd pos).copy, t₂, ?_, by simp⟩
  simp only [ByteString.Slice.startPos_copy, get_toCopy, get_eq_get_ofReplaceStart, ofReplaceStart_startPos] at ht₂
  rw [append_assoc, ← ht₂, ← copy_eq_copy_replaceEnd]

def FirstByte.utf8ByteSize : FirstByte → ByteString.ByteOffset
  | .invalid => ⟨0⟩
  | .done => ⟨1⟩
  | .oneMore => ⟨2⟩
  | .twoMore => ⟨3⟩
  | .threeMore => ⟨4⟩

def UInt8.utf8ByteSize (c : UInt8) (_h : c.IsUtf8FirstByte) : ByteString.ByteOffset :=
  if c &&& 0x80 == 0 then
    ⟨1⟩
  else if c &&& 0xe0 == 0xc0 then
    ⟨2⟩
  else if c &&& 0xf0 == 0xe0 then
    ⟨3⟩
  else
    ⟨4⟩

theorem UInt8.utf8ByteSize_eq_utf8ByteSize_parseFirstByte {c : UInt8} {h : c.IsUtf8FirstByte} :
    c.utf8ByteSize h = (parseFirstByte c).utf8ByteSize := by
  grind [utf8ByteSize, FirstByte.utf8ByteSize, parseFirstByte, IsUtf8FirstByte]

theorem utf8ByteSize_getElem_utf8EncodeChar {c : Char} :
    ((String.utf8EncodeChar c)[0]'(by simp [c.utf8Size_pos])).utf8ByteSize
      isUtf8FirstByte_getElem_zero_utf8EncodeChar = c.utf8Size' := by
  rw [UInt8.utf8ByteSize_eq_utf8ByteSize_parseFirstByte]
  simp only [ByteString.ByteOffset.ext_iff, Char.numBytes_utf8Size']
  obtain (hc|hc|hc|hc) := c.utf8Size_eq
  · rw [parseFirstByte_utf8EncodeChar_eq_done hc, FirstByte.utf8ByteSize, hc]
  · rw [parseFirstByte_utf8EncodeChar_eq_oneMore hc, FirstByte.utf8ByteSize, hc]
  · rw [parseFirstByte_utf8EncodeChar_eq_twoMore hc, FirstByte.utf8ByteSize, hc]
  · rw [parseFirstByte_utf8EncodeChar_eq_threeMore hc, FirstByte.utf8ByteSize, hc]

theorem utf8Size'_utf8DecodeChar {b : ByteArray} {i} {h} :
    (utf8DecodeChar b i h).utf8Size' =
      (b[i]'(lt_size_of_isSome_utf8DecodeChar? h)).utf8ByteSize (isUtf8FirstByte_of_isSome_utf8DecodeChar? h) := by
  rw [← utf8ByteSize_getElem_utf8EncodeChar]
  simp only [List.getElem_eq_getElem_toByteArray, utf8EncodeChar_utf8DecodeChar]
  simp [ByteArray.getElem_extract]

theorem ByteString.Slice.Pos.utf8ByteSize_byte {s : ByteString.Slice} {pos : s.Pos} {h : pos ≠ s.endPos} :
    (pos.byte h).utf8ByteSize pos.isUtf8FirstByte_byte = (pos.get h).utf8Size' := by
  simp only [Pos.get, utf8Size'_utf8DecodeChar, Pos.byte, Slice.utf8ByteAt, ByteString.utf8ByteAt,
    ByteOffset.numBytes_add]

def ByteString.Slice.Pos.next {s : ByteString.Slice} (pos : s.Pos) (h : pos ≠ s.endPos) : s.Pos where
  offset := pos.offset + (pos.byte h).utf8ByteSize pos.isUtf8FirstByte_byte
  validOffset := by
    obtain ⟨t₁, t₂, ht, ht'⟩ := copy_eq_append_get h
    rw [utf8ByteSize_byte, ← validOffset_copy_iff, ht, ← ht']
    refine ValidOffset.append_right ?_ t₂
    refine ValidOffset.append_left ?_ t₁
    exact validOffset_singleton_utf8Size'

def ByteString.Slice.Pos.next? {s : ByteString.Slice} (pos : s.Pos) : Option s.Pos :=
  if h : pos = s.endPos then none else some (pos.next h)

def ByteString.Slice.Pos.next! {s : ByteString.Slice} (pos : s.Pos) : s.Pos :=
  if h : pos = s.endPos then panic! "Cannot advance the end position" else pos.next h

def ByteString.Slice.Pos.prevAux {s : ByteString.Slice} (pos : s.Pos) (h : pos ≠ s.startPos) :
    ByteString.ByteOffset :=
  go ⟨pos.offset.numBytes - 1⟩ (by
    have := pos.validOffset.le_utf8Size
    simp only [ByteOffset.le_iff_numBytes_le, numBytes_utf8Size, ne_eq, Pos.ext_iff,
      offset_startPos, ByteOffset.ext_iff, ByteOffset.numBytes_zero, ByteOffset.lt_iff_numBytes_lt] at ⊢ this h
    omega)
where
  go (off : ByteString.ByteOffset) (h₁ : off < s.utf8Size) : ByteString.ByteOffset :=
    if hbyte : (s.utf8ByteAt off h₁).isUtf8FirstByte then
      off
    else
      have : 0 ≠ off.numBytes := by
        intro h
        obtain rfl : off = 0 := by simpa [ByteOffset.ext_iff] using h.symm
        simp [UInt8.isUtf8FirstByte_eq_true.2 (s.isUtf8FirstByte_utf8ByteAt_zero h₁)] at hbyte
      go ⟨off.numBytes - 1⟩ (by simp [ByteOffset.lt_iff_numBytes_lt] at ⊢ h₁; omega)
  termination_by off.numBytes

theorem ByteString.Slice.Pos.validOffset_prevAuxGo {s : ByteString.Slice} (off : ByteString.ByteOffset) (h₁ : off < s.utf8Size) :
    s.ValidOffset (ByteString.Slice.Pos.prevAux.go off h₁) := by
  fun_induction prevAux.go with
  | case1 off h h' =>
    refine (s.validOffset_iff_isUtf8FirstByte off).2 (Or.inr ⟨h, ?_⟩)
    exact UInt8.isUtf8FirstByte_eq_true.1 h'
  | case2 => assumption

theorem ByteString.Slice.Pos.validOffset_prevAux {s : ByteString.Slice} (pos : s.Pos) (h : pos ≠ s.startPos) :
    s.ValidOffset (pos.prevAux h) := by
  rw [prevAux]
  apply ByteString.Slice.Pos.validOffset_prevAuxGo

def ByteString.Slice.Pos.prev {s : ByteString.Slice} (pos : s.Pos) (h : pos ≠ s.startPos) : s.Pos where
  offset := prevAux pos h
  validOffset := validOffset_prevAux pos h

def ByteString.Slice.pos (s : ByteString.Slice) (off : ByteString.ByteOffset) (h : s.ValidOffset off) : s.Pos where
  offset := off
  validOffset := h

def ByteString.Slice.pos? (s : ByteString.Slice) (off : ByteString.ByteOffset) : Option s.Pos :=
  if h : s.isValidOffset off then
    some (s.pos off (s.isValidOffset_eq_true.1 h))
  else
    none

def ByteString.Slice.pos! (s : ByteString.Slice) (off : ByteString.ByteOffset) : s.Pos :=
  if h : s.isValidOffset off then
    s.pos off (s.isValidOffset_eq_true.1 h)
  else
    panic! "Offset is not at a valid UTF-8 character boundary"

def ByteString.Pos.next? {s : ByteString} (pos : s.Pos) : Option s.Pos :=
  pos.toSlice.next?.map ByteString.Slice.Pos.ofSlice

def ByteString.Pos.next! {s : ByteString} (pos : s.Pos) : s.Pos :=
  pos.toSlice.next!.ofSlice

def ByteString.pos (s : ByteString) (off : ByteString.ByteOffset) (h : s.ValidOffset off) : s.Pos :=
  (s.toSlice.pos off h.toSlice).ofSlice

def ByteString.pos? (s : ByteString) (off : ByteString.ByteOffset) : Option s.Pos :=
  (s.toSlice.pos? off).map ByteString.Slice.Pos.ofSlice

def ByteString.pos! (s : ByteString) (off : ByteString.ByteOffset) : s.Pos :=
  (s.toSlice.pos! off).ofSlice

def ByteString.Pos.cast {s t : ByteString} (pos : s.Pos) (h : s = t) : t.Pos where
  offset := pos.offset
  validOffset := h ▸ pos.validOffset

def ByteString.Pos.next {s : ByteString} (pos : s.Pos) (h : pos ≠ s.endPos) : s.Pos :=
  (pos.toSlice.next (ne_of_apply_ne Slice.Pos.ofSlice (by simpa))).ofSlice

@[simp]
theorem ByteString.Pos.offset_cast {s t : ByteString} {pos : s.Pos} {h : s = t} :
    (pos.cast h).offset = pos.offset := rfl

def ByteString.appendSlice (s : ByteString) (t : ByteString.Slice) : ByteString where
  bytes := ByteArray.copySlice t.str.bytes t.startInclusive.offset.numBytes s.bytes s.bytes.size t.utf8Size.numBytes false
  isValidUtf8 := by
    rw [ByteArray.copySlice_eq_append]
    simp only [ByteArray.extract_zero_size, Slice.numBytes_utf8Size, ByteArray.size_data,
      ByteArray.extract_add_left, ByteArray.append_empty]
    refine s.isValidUtf8.append ?_
    have := ByteOffset.le_iff_numBytes_le.1 t.startInclusive_le_endExclusive
    simp only [this, Nat.add_sub_cancel']
    simpa only [← t.bytes_copy] using t.copy.isValidUtf8

instance : HAppend ByteString ByteString.Slice ByteString where
  hAppend s t := s.appendSlice t

def ByteString.Slice.append (s t : ByteString.Slice) : ByteString :=
  s.copy ++ t

instance : HAppend ByteString.Slice ByteString.Slice ByteString where
  hAppend s t := s.append t

def ByteString.Slice.appendString (s : ByteString.Slice) (t : ByteString) : ByteString :=
  s.copy ++ t

instance : HAppend ByteString.Slice ByteString ByteString where
  hAppend s t := s.appendString t

def ByteString.Pos.appendRight {s : ByteString} (pos : s.Pos) (t : ByteString) : (s ++ t).Pos where
  offset := pos.offset
  validOffset := pos.validOffset.append_right t

@[simp]
theorem ByteString.Pos.offset_appendRight {s : ByteString} {pos : s.Pos} {t : ByteString} : (pos.appendRight t).offset = pos.offset :=
  rfl

def ByteString.Pos.appendLeft {s : ByteString} (pos : s.Pos) (t : ByteString) : (t ++ s).Pos where
  offset := t.utf8Size + pos.offset
  validOffset := pos.validOffset.append_left t

@[simp]
theorem ByteString.Pos.offset_appendLeft {s : ByteString} {pos : s.Pos} {t : ByteString} : (pos.appendLeft t).offset = t.utf8Size + pos.offset :=
  rfl
