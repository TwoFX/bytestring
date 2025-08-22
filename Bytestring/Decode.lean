import Bytestring.ByteArray

section decode

inductive FirstByte where
  | invalid : FirstByte
  | done : FirstByte
  | oneMore : FirstByte
  | twoMore : FirstByte
  | threeMore : FirstByte

inductive LaterByte where
  | invalid : LaterByte
  | valid : (b : UInt8) → b < 0x40 → LaterByte

instance : Trans (· ≤ · : UInt8 → UInt8 → Prop) (· < · : UInt8 → UInt8 → Prop) (· < ·) where
  trans := UInt8.lt_of_le_of_lt

-- abbrev UInt8.maxValue : UInt8 := 0xFF

-- @[simp] theorem UInt8.toBitVec_maxValue : UInt8.maxValue.toBitVec = BitVec.allOnes _ := rfl

-- @[simp] theorem UInt8.and_maxValue {b : UInt8} : b &&& UInt8.maxValue = b :=
--   UInt8.eq_of_toBitVec_eq (by rw [UInt8.toBitVec_and, toBitVec_maxValue, BitVec.and_allOnes])

theorem BitVec.and_or_distrib_left {a b c : BitVec w} : a &&& (b ||| c) = (a &&& b) ||| (a &&& c) :=
  BitVec.eq_of_getElem_eq (by simp [Bool.and_or_distrib_left])

theorem BitVec.and_or_distrib_right {a b c : BitVec w} : (a ||| b) &&& c = (a &&& c) ||| (b &&& c) :=
  BitVec.eq_of_getElem_eq (by simp [Bool.and_or_distrib_right])

theorem UInt8.and_or_distrib_left {a b c : UInt8} : a &&& (b ||| c) = (a &&& b) ||| (a &&& c) :=
  UInt8.eq_of_toBitVec_eq (by simp [BitVec.and_or_distrib_left])

theorem UInt8.and_or_distrib_right {a b c : UInt8} : (a ||| b) &&& c = (a &&& c) ||| (b &&& c) :=
  UInt8.eq_of_toBitVec_eq (by simp [BitVec.and_or_distrib_right])

theorem UInt8.le_of_and_not_eq_zero {b c : UInt8} (h : b &&& ~~~c = 0) : b ≤ c :=
  calc
    b = b &&& (c ||| ~~~c) := by simp
    _ = b &&& c := by simp only [UInt8.and_or_distrib_left, h, UInt8.or_zero]
    _ ≤ c := and_le_right

theorem BitVec.length_pos_of_lt {b b' : BitVec w} (h : b < b') : 0 < w :=
  length_pos_of_ne (BitVec.ne_of_lt h)

theorem BitVec.not_lt_iff {b : BitVec w} : ~~~b < b ↔ 0 < w ∧ b.msb = true := by
  refine ⟨fun h => ?_, fun ⟨hw, hb⟩ => ?_⟩
  · have := length_pos_of_lt h
    exact ⟨this, by rwa [← ult_iff_lt, ult_eq_msb_of_msb_neq (by simp_all)] at h⟩
  · rwa [← ult_iff_lt, ult_eq_msb_of_msb_neq (by simp_all)]

theorem UInt8.not_lt_iff {b : UInt8} : ~~~b < b ↔ b.toBitVec.msb = true := by
  simp [UInt8.lt_iff_toBitVec_lt, BitVec.not_lt_iff]

theorem UInt8.lt_of_and_eq_zero {b c : UInt8} (h : b &&& c = 0) (h' : c.toBitVec.msb = true) : b < c :=
  calc
    b ≤ ~~~c := UInt8.le_of_and_not_eq_zero (by simp [h])
    _ < c := UInt8.not_lt_iff.2 h'

theorem UInt8.lt_0x80_of_and_eq_zero {b : UInt8} (h : b &&& 0x80 = 0) : b < 0x80 :=
  UInt8.lt_of_and_eq_zero h (by decide)

theorem UInt8.lt_add_one {c : UInt8} (h : c ≠ -1) : c < c + 1 := by
  rw [Ne, ← UInt8.toNat_inj, ← Ne] at h
  simp only [toNat_neg, UInt8.reduceToNat, Nat.add_one_sub_one, Nat.mod_succ, ne_eq] at h
  rw [UInt8.lt_iff_toNat_lt, UInt8.toNat_add]
  simp only [UInt8.reduceToNat, Nat.reducePow]

  rw [Nat.mod_eq_of_lt (by have := c.toNat_lt; omega)]
  omega

theorem UInt8.and_lt_add_one {b c : UInt8} (h : c ≠ -1) : b &&& c < c + 1 :=
  UInt8.lt_of_le_of_lt UInt8.and_le_right (UInt8.lt_add_one h)

@[inline]
def parseFirstByte (b : UInt8) : FirstByte :=
  if b < 128 then
    .done
  else if b &&& 0xe0 == 0xc0 then
    .oneMore
  else if b &&& 0xf0 == 0xe0 then
    .twoMore
  else if b &&& 0xf8 == 0xf0 then
    .threeMore
  else .invalid

theorem parseFirstByte_eq_done (b : UInt8) (hb : b ≤ 127) : parseFirstByte b = .done := by
  grind [parseFirstByte]

theorem parseFirstByte_eq_oneMore (b : UInt8) (hb₁ : 128 ≤ b) (hb₂ : b &&& 0xe0 = 0xc0) :
    parseFirstByte b = .oneMore := by
  grind [parseFirstByte]

@[inline]
def isInvalidContinuationByte (b : UInt8) : Bool :=
  b &&& 0xc0 != 0x80

theorem isInvalidContinutationByte_eq_false_iff {b : UInt8} :
    isInvalidContinuationByte b = false ↔ b &&& 0xc0 = 0x80 := by
  simp [isInvalidContinuationByte]

-- @[inline]
-- def parseLaterByte (b : UInt8) : LaterByte :=
--   if b &&& 0xc0 == 0x80 then
--     .valid (b &&& 0x3f) (UInt8.and_lt_add_one (by decide))
--   else .invalid

-- theorem parseLaterByte_eq_valid (b : UInt8) (hb : b &&& 0xc0 = 0x80) :
--     parseLaterByte b = .valid (b &&& 0x3f) (UInt8.and_lt_add_one (by decide)) := by
--   grind [parseLaterByte]

@[inline]
def utf8DecodeChar? (bytes : ByteArray) (i : Nat) : Option Char :=
  if h₀ : i < bytes.size then
    match h : parseFirstByte bytes[i] with
    | .invalid => none -- invalid first byte
    | .done => some ⟨bytes[i].toUInt32, ?done⟩
    | .oneMore =>
      let b₀ : UInt8 := bytes[i] &&& 0x1f
      if h₁ : i +  1 < bytes.size then
        if isInvalidContinuationByte bytes[i + 1] then
          none
        else
          let b₁ := bytes[i + 1] &&& 0x3f
          let r := (b₀.toUInt32 <<< 6) ||| b₁.toUInt32
          if r < 0x80 then
            none -- overlong encoding
          else
            some ⟨r, ?onemore⟩
      else none
    | .twoMore =>
      let b₀ : UInt8 := bytes[i] &&& 0x0f
      if h₁ : i + 2 < bytes.size then
        if isInvalidContinuationByte bytes[i + 1] || isInvalidContinuationByte bytes[i + 2] then
          none
        else
          let b₁ := bytes[i + 1] &&& 0x3f
          let b₂ := bytes[i + 2] &&& 0x3f
          let r := (b₀.toUInt32 <<< 12) ||| (b₁.toUInt32 <<< 6) ||| b₂.toUInt32
          if r < 0x800 then
            none -- overlong encoding
          else if hr : 0xd800 ≤ r ∧ r ≤ 0xdfff then
            none -- surrogate code point
          else
            some ⟨r, ?twomore⟩
      else none
    | .threeMore =>
      let b₀ : UInt8 := bytes[i] &&& 0x07
      if h₁ : i + 3 < bytes.size then
        if isInvalidContinuationByte bytes[i + 1] || isInvalidContinuationByte bytes[i + 2] || isInvalidContinuationByte bytes[i + 3] then
          none
        else
          let b₁ := bytes[i + 1] &&& 0x3f
          let b₂ := bytes[i + 2] &&& 0x3f
          let b₃ := bytes[i + 3] &&& 0x3f
          let r := (b₀.toUInt32 <<< 18) ||| (b₁.toUInt32 <<< 12) ||| (b₂.toUInt32 <<< 6) ||| b₃.toUInt32
          if h₁ : r < 0x10000 then
            none -- overlong encoding
          else if h₂ : 0x10ffff < r then
            none -- out-of-range code point
          else
            some ⟨r, ?threemore⟩
      else none
  else none
where finally
  case done => grind [parseFirstByte, UInt8.lt_iff_toNat_lt, UInt8.toNat_toUInt32]
  case onemore =>
    have hb₀ : b₀ < 0x20 := UInt8.and_lt_add_one (by decide)
    have hb₁ : b₁ < 0x40 := UInt8.and_lt_add_one (by decide)
    refine Or.inl ?_
    subst r
    simp only [UInt8.lt_iff_toNat_lt, UInt8.reduceToNat] at hb₀ hb₁
    simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, UInt32.reduceToNat,
      Nat.reduceMod, Nat.reducePow]
    rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hb₁]
    omega
  case twomore =>
    have hb₀ : b₀ < 0x10 := UInt8.and_lt_add_one (by decide)
    have hb₁ : b₁ < 0x40 := UInt8.and_lt_add_one (by decide)
    have hb₂ : b₂ < 0x40 := UInt8.and_lt_add_one (by decide)
    simp only [UInt8.lt_iff_toNat_lt, UInt8.reduceToNat] at hb₀ hb₁ hb₂
    simp only [Decidable.not_and_iff_not_or_not, UInt32.not_le] at hr
    rcases hr with (hr|hr)
    · exact Or.inl hr
    · refine Or.inr ⟨hr, ?_⟩
      subst r
      simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, UInt32.reduceToNat,
        Nat.reduceMod, Nat.reducePow]
      rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mul_comm _ (2 ^ _), Nat.mul_comm _ (2 ^ _), Nat.or_assoc, ← Nat.two_pow_add_eq_or_of_lt (b := b₂.toNat) hb₂,
          ← Nat.two_pow_add_eq_or_of_lt (by omega)]
      omega
  case threemore =>
    have hb₀ : b₀ < 0x08 := UInt8.and_lt_add_one (by decide)
    have hb₁ : b₁ < 0x40 := UInt8.and_lt_add_one (by decide)
    have hb₂ : b₂ < 0x40 := UInt8.and_lt_add_one (by decide)
    have hb₃ : b₃ < 0x40 := UInt8.and_lt_add_one (by decide)
    simp only [UInt8.lt_iff_toNat_lt, UInt8.reduceToNat] at hb₀ hb₁ hb₂ hb₃
    simp only [UInt32.not_lt, UInt32.le_iff_toNat_le, UInt32.reduceToNat] at h₁ h₂
    exact Or.inr ⟨by omega, by omega⟩

def utf8DecodeChar (bytes : ByteArray) (i : Nat) (h : (utf8DecodeChar? bytes i).isSome) : Char :=
  (utf8DecodeChar? bytes i).get h

theorem utf8DecodeChar?_utf8EncodeChar_append {b : ByteArray} {c : Char} :
    utf8DecodeChar? ((String.utf8EncodeChar c).toByteArray ++ b) 0 = some c := by
  fun_cases String.utf8EncodeChar c with
  | case1 v h =>
    rw [utf8DecodeChar?, dif_pos (by simp; grind [Char.utf8Size_pos])]
    have : parseFirstByte ([v.toUInt8].toByteArray ++ b)[0] = .done := by
      rw [parseFirstByte_eq_done]
      simp [UInt8.le_iff_toNat_le, UInt32.le_iff_toNat_le] at h ⊢
      grind
    split <;> rename_i h' <;> try (simp_all; done)
    · simp only [Option.some.injEq]
      ext
      simp
      grind
  | case2 v h₁ h₂ =>
    rw [utf8DecodeChar?, dif_pos (by simp; grind [Char.utf8Size_pos])]
    sorry
    -- rw [parseFirstByte_eq_oneMore]
    -- · simp only
    --   rw [dif_pos (by simp; grind)]
    --   simp only [Nat.zero_add, List.size_toByteArray, List.length_cons, List.length_nil,
    --     Nat.reduceAdd, Nat.lt_add_one, ByteArray.getElem_append_left, List.getElem_toByteArray,
    --     List.getElem_cons_succ, List.getElem_cons_zero, Nat.zero_lt_succ, UInt8.toUInt32_and,
    --     UInt8.toUInt32_or, UInt32.toUInt32_toUInt8, Nat.reduceLT, UInt8.toUInt32_ofNat]
    --   rw [parseLaterByte_eq_valid]
    --   · simp only [UInt8.toUInt32_and, UInt8.toUInt32_or, UInt32.toUInt32_toUInt8, Nat.reduceLT,
    --       UInt8.toUInt32_ofNat, Option.ite_none_left_eq_some, UInt32.not_lt, Option.some.injEq]
    --     refine ⟨?_, ?_⟩
    --     · sorry
    --     · ext
    --       simp
    --       sorry
    --   · sorry
    -- · simp
    --   sorry
    -- · simp
    --   sorry
  | case3 => sorry
  | case4 => sorry

theorem String.utf8EncodeChar_eq_singleton {c : Char} (hc : c.val < 128) :
    String.utf8EncodeChar c = [c.val.toUInt8] := by
  grind [utf8EncodeChar]

theorem String.utf8EncodeChar_eq_cons_cons {c : Char} (hc₀ : 128 ≤ c.val) (hc₁ : c.val ≤ 0x7ff) :
    String.utf8EncodeChar c = [(c.val >>>  6).toUInt8 &&& 0x1f ||| 0xc0, c.val.toUInt8 &&& 0x3f ||| 0x80] := by
  grind [utf8EncodeChar]

theorem String.utf8EncodeChar_eq_cons_cons_cons {c : Char} (hc₀ : 0x7ff < c.val) (hc₁ : c.val ≤ 0xffff) :
    String.utf8EncodeChar c =
    [(c.val >>> 12).toUInt8 &&& 0x0f ||| 0xe0,
     (c.val >>>  6).toUInt8 &&& 0x3f ||| 0x80,
              c.val.toUInt8 &&& 0x3f ||| 0x80] := by
  grind [utf8EncodeChar]

theorem String.utf8EncodeChar_eq_cons_cons_cons_cons {c : Char} (hc : 0xffff < c.val) :
    String.utf8EncodeChar c =
    [(c.val >>> 18).toUInt8 &&& 0x07 ||| 0xf0,
     (c.val >>> 12).toUInt8 &&& 0x3f ||| 0x80,
     (c.val >>>  6).toUInt8 &&& 0x3f ||| 0x80,
              c.val.toUInt8 &&& 0x3f ||| 0x80] := by
  grind [utf8EncodeChar]

theorem eq_of_utf8DecodeChar?_eq_some {b : ByteArray} {c : Char} (h : utf8DecodeChar? b 0 = some c) :
    b = (String.utf8EncodeChar c).toByteArray ++ b.extract c.utf8Size b.size := by
  conv => lhs; rw [← ByteArray.extract_zero_size (b := b), ByteArray.extract_eq_extract_append_extract (min c.utf8Size b.size) (by simp) (Nat.min_le_right ..)]
  congr 1
  · revert h
    fun_cases utf8DecodeChar? b 0
    all_goals try (simp; done)
    all_goals (simp only [Option.some.injEq]); rintro rfl
    · rename_i hb hp
      rw [← String.length_utf8EncodeChar, String.utf8EncodeChar_eq_singleton]
      · simp only [UInt8.toUInt8_toUInt32, List.length_cons, List.length_nil, Nat.zero_add,
        (by omega : min 1 b.size = 1)]
        rw [ByteArray.extract_add_one (by omega)]
      · simp [UInt32.lt_iff_toNat_lt]
        grind [parseFirstByte, UInt8.lt_iff_toNat_lt]
    · rename_i _ hp b₀ hb hb₁ b₁ r hr
      subst b₀ b₁ r
      rw [← String.length_utf8EncodeChar, String.utf8EncodeChar_eq_cons_cons]
      · simp [(by omega : min 2 b.size = 2)]
        rw [ByteArray.extract_add_two (by omega)]
        congr
        · sorry
        · sorry
      · grind
      · simp [UInt32.le_iff_toNat_le]
        · sorry
    · rename_i _ hp b₀ hb hb₁₂ b₁ b₂ r hr₁ hr₂
      subst b₀ b₁ b₂ r
      rw [← String.length_utf8EncodeChar, String.utf8EncodeChar_eq_cons_cons_cons]
      · simp [(by omega : min 3 b.size = 3)]
        rw [ByteArray.extract_add_three (by omega)]
        congr
        · sorry
        · sorry
        · sorry
      · grind
      · sorry
    · rename_i _ hp b₀ hb hb₁₂₃ b₁ b₂ b₃ r hr₁ hr₂
      subst b₀ b₁ b₂ b₃ r
      rw [← String.length_utf8EncodeChar, String.utf8EncodeChar_eq_cons_cons_cons_cons]
      · simp [(by omega : min 4 b.size = 4)]
        rw [ByteArray.extract_add_four (by omega)]
        simp [isInvalidContinutationByte_eq_false_iff] at hb₁₂₃
        congr
        · sorry
        · sorry
        · sorry
        · sorry
      · grind
  · simp only [ByteArray.extract_eq_extract_left, Nat.le_refl, Nat.min_eq_left]
    omega

theorem exists_of_utf8DecodeChar?_eq_some {b : ByteArray} {c : Char} (h : utf8DecodeChar? b 0 = some c) :
    ∃ l, b = (String.utf8EncodeChar c).toByteArray ++ l :=
  ⟨b.extract c.utf8Size b.size, eq_of_utf8DecodeChar?_eq_some h⟩

theorem utf8DecodeChar?_eq_utf8DecodeChar?_drop {b : ByteArray} {i : Nat} :
    utf8DecodeChar? b i = utf8DecodeChar? (b.extract i b.size) 0 := by
  simp [utf8DecodeChar?]
  have h₁ : i < b.size ↔ 0 < b.size - i := by omega
  have h₂ : i + 1 < b.size ↔ 1 < b.size - i := by omega
  have h₃ : i + 2 < b.size ↔ 2 < b.size - i := by omega
  have h₄ : i + 3 < b.size ↔ 3 < b.size - i := by omega
  have h₅ : ∀ h, b[i]'h = (b.extract i b.size)[0]'(by simp; omega) := by simp [ByteArray.getElem_extract]
  have h₆ : ∀ h, b[i + 1]'h = (b.extract i b.size)[1]'(by simp; omega) := by simp [ByteArray.getElem_extract]
  have h₇ : ∀ h, b[i + 2]'h = (b.extract i b.size)[2]'(by simp; omega) := by simp [ByteArray.getElem_extract]
  have h₈ : ∀ h, b[i + 3]'h = (b.extract i b.size)[3]'(by simp; omega) := by simp [ByteArray.getElem_extract]
  have h₉ : (b.extract i b.size).size = b.size - i := by simp
  simp only [h₁]
  split
  · split
    all_goals (rename_i h h'; simp only [h₅] at h')
    · split <;> simp_all
    · split <;> rename_i h''
      all_goals try (simp [h'] at h''; done)
      simp [h₅]
    · symm
      split <;> rename_i h''
      all_goals try (simp [h'] at h''; done)
      simp [h₂, h₅, h₆]
    · symm
      split <;> rename_i h''
      all_goals try (simp [h'] at h''; done)
      simp [h₃, h₅, h₆, h₇]
    · symm
      split <;> rename_i h''
      all_goals try (simp [h'] at h''; done)
      simp [h₄, h₅, h₆, h₇, h₈]
  · rfl

  -- grind

theorem le_size_of_utf8DecodeChar?_eq_some {b : ByteArray} {i : Nat} {c : Char}
    (h : utf8DecodeChar? b i = some c) : i + c.utf8Size ≤ b.size := by
  rw [utf8DecodeChar?_eq_utf8DecodeChar?_drop] at h
  obtain ⟨l, hl⟩ := exists_of_utf8DecodeChar?_eq_some h
  replace hl := congrArg ByteArray.size hl
  simp at hl
  have hi : i < b.size := by
    simp [utf8DecodeChar?] at h
    obtain ⟨h, -⟩ := h
    omega
  omega

end decode
