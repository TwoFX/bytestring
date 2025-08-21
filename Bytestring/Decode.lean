import Bytestring.ByteArray

section decode

inductive FirstByte where
  | invalid : FirstByte
  | done : (b : UInt8) → b < 0x80 → FirstByte
  | oneMore : (b : UInt8) → b < 0x20 → FirstByte
  | twoMore : (b : UInt8) → b < 0x10 → FirstByte
  | threeMore : (b : UInt8) → b < 0x08 → FirstByte

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
  if h : b < 128 then
    .done b h
  else if b &&& 0xe0 == 0xc0 then
    .oneMore (b &&& 0x1f) (UInt8.and_lt_add_one (by decide))
  else if b &&& 0xf0 == 0xe0 then
    .twoMore (b &&& 0x0f) (UInt8.and_lt_add_one (by decide))
  else if b &&& 0xf8 == 0xf0 then
    .threeMore (b &&& 0x07) (UInt8.and_lt_add_one (by decide))
  else .invalid

theorem parseFirstByte_eq_done (b : UInt8) (hb : b ≤ 127) : parseFirstByte b = .done b (by grind only) := by
  grind [parseFirstByte]

theorem parseFirstByte_eq_oneMore (b : UInt8) (hb₁ : 128 ≤ b) (hb₂ : b &&& 0xe0 = 0xc0) :
    parseFirstByte b = .oneMore (b &&& 0x1f) (UInt8.and_lt_add_one (by decide)) := by
  grind [parseFirstByte]

@[inline]
def parseLaterByte (b : UInt8) : LaterByte :=
  if b &&& 0xc0 == 0x80 then
    .valid (b &&& 0x3f) (UInt8.and_lt_add_one (by decide))
  else .invalid

theorem parseLaterByte_eq_valid (b : UInt8) (hb : b &&& 0xc0 = 0x80) :
    parseLaterByte b = .valid (b &&& 0x3f) (UInt8.and_lt_add_one (by decide)) := by
  grind [parseLaterByte]

@[inline]
def utf8DecodeChar? (bytes : ByteArray) (i : Nat) : Option Char :=
  if h₀ : i < bytes.size then
    match parseFirstByte bytes[i] with
    | .invalid => none -- invalid first byte
    | .done b₀ hb₀ => some ⟨b₀.toUInt32, ?done⟩
    | .oneMore b₀ hb₀ =>
      if h₁ : i + 1 < bytes.size then
        match parseLaterByte bytes[i + 1] with
        | .invalid => none -- invalid second byte
        | .valid b₁ hb₁ =>
          let r := (b₀.toUInt32 <<< 6) ||| b₁.toUInt32
          if r < 0x80 then
            none -- overlong encoding
          else
            some ⟨r, ?onemore⟩
      else none
    | .twoMore b₀ hb₀ =>
      if h₁ : i + 2 < bytes.size then
        let c₁ := bytes[i + 1]
        let c₂ := bytes[i + 2]
        match parseLaterByte bytes[i + 1], parseLaterByte bytes[i + 2] with
        | .invalid, .invalid => none -- invalid second/third byte
        | .valid _ _, .invalid => none -- invalid third byte
        | .invalid, .valid _ _ => none -- invalid second byte
        | .valid b₁ hb₁, .valid b₂ hb₂ =>
          let r := (b₀.toUInt32 <<< 12) ||| (b₁.toUInt32 <<< 6) ||| b₂.toUInt32
          if r < 0x800 then
            none -- overlong encoding
          else if hr : 0xd800 ≤ r ∧ r ≤ 0xdfff then
            none -- surrogate code point
          else
            some ⟨r, ?twomore⟩
      else none
    | .threeMore b₀ hb₀ =>
      if h₁ : i + 3 < bytes.size then
        let c₁ := bytes[i + 1]
        let c₂ := bytes[i + 2]
        let c₃ := bytes[i + 3]
        match parseLaterByte bytes[i + 1], parseLaterByte bytes[i + 2], parseLaterByte bytes[i + 3] with
        | .invalid, .invalid, .invalid => none -- invalid second/third/fourth byte
        | .valid _ _, .invalid, .invalid => none -- invalid third/fouth byte
        | .invalid, .valid _ _, .invalid => none -- invalid second/fourth byte
        | .valid _ _, .valid _ _, .invalid => none -- invalid fourth byte
        | .invalid, .invalid, .valid _ _ => none -- invalid second/third byte
        | .valid _ _, .invalid, .valid _ _ => none -- invalid third byte
        | .invalid, .valid _ _, .valid _ _ => none -- invalid second byte
        | .valid b₁ hb₁, .valid b₂ hb₂, .valid b₃ hb₃ =>
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
  case done => grind [UInt8.lt_iff_toNat_lt, UInt8.toNat_toUInt32]
  case onemore =>
    refine Or.inl ?_
    subst r
    simp only [UInt8.lt_iff_toNat_lt, UInt8.reduceToNat] at hb₀ hb₁
    simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, UInt32.reduceToNat,
      Nat.reduceMod, Nat.reducePow]
    rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hb₁]
    omega
  case twomore =>
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
    rw [parseFirstByte_eq_done]
    · simp only [Option.some.injEq]
      ext
      simp
      grind
    · simp [UInt8.le_iff_toNat_le, UInt32.le_iff_toNat_le] at h ⊢
      grind
  | case2 v h₁ h₂ =>
    rw [utf8DecodeChar?, dif_pos (by simp; grind [Char.utf8Size_pos])]
    rw [parseFirstByte_eq_oneMore]
    · simp only
      rw [dif_pos (by simp; grind)]
      simp only [Nat.zero_add, List.size_toByteArray, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.lt_add_one, ByteArray.getElem_append_left, List.getElem_toByteArray,
        List.getElem_cons_succ, List.getElem_cons_zero, Nat.zero_lt_succ, UInt8.toUInt32_and,
        UInt8.toUInt32_or, UInt32.toUInt32_toUInt8, Nat.reduceLT, UInt8.toUInt32_ofNat]
      rw [parseLaterByte_eq_valid]
      · simp only [UInt8.toUInt32_and, UInt8.toUInt32_or, UInt32.toUInt32_toUInt8, Nat.reduceLT,
          UInt8.toUInt32_ofNat, Option.ite_none_left_eq_some, UInt32.not_lt, Option.some.injEq]
        refine ⟨?_, ?_⟩
        · sorry
        · ext
          simp
          sorry
      · sorry
    · simp
      sorry
    · simp
      sorry
  | case3 => sorry
  | case4 => sorry

theorem eq_of_utf8DecodeChar?_eq_some {b : ByteArray} {c : Char} (h : utf8DecodeChar? b 0 = some c) :
    b = (String.utf8EncodeChar c).toByteArray ++ b.extract c.utf8Size b.size := by
  ext
  simp
  sorry
  sorry

theorem exists_of_utf8DecodeChar?_eq_some {b : ByteArray} {c : Char} (h : utf8DecodeChar? b 0 = some c) :
    ∃ l, b = (String.utf8EncodeChar c).toByteArray ++ l :=
  ⟨b.extract c.utf8Size b.size, eq_of_utf8DecodeChar?_eq_some h⟩

theorem utf8DecodeChar?_eq_utf8DecodeChar?_drop {b : ByteArray} {i : Nat} :
    utf8DecodeChar? b i = utf8DecodeChar? (b.extract i b.size) 0 := by
  simp [utf8DecodeChar?]
  have : i < b.size ↔ 0 < b.size - i := by omega
  have : i + 1 < b.size ↔ 1 < b.size - i := by omega
  have : i + 2 < b.size ↔ 2 < b.size - i := by omega
  have : i + 3 < b.size ↔ 3 < b.size - i := by omega
  have : ∀ h h', b[i]'h = (b.extract i b.size)[0]'h' := by simp [ByteArray.getElem_extract]
  have : ∀ h h', b[i + 1]'h = (b.extract i b.size)[1]'h' := by simp [ByteArray.getElem_extract]
  have : ∀ h h', b[i + 2]'h = (b.extract i b.size)[2]'h' := by simp [ByteArray.getElem_extract]
  have : ∀ h h', b[i + 3]'h = (b.extract i b.size)[3]'h' := by simp [ByteArray.getElem_extract]
  have : (b.extract i b.size).size = b.size - i := by simp
  grind

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
