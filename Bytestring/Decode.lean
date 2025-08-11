
section decode

inductive FirstByte where
  | invalid : FirstByte
  | done : (b : UInt8) → b < 0x80 → FirstByte
  | oneMore : (b : UInt8) → b < 0x20 → FirstByte
  | twoMore : (b : UInt8) → b < 0x10 → FirstByte
  | threeMore : (b : UInt8) → b < 0x08 → FirstByte

instance : Trans (· ≤ · : UInt8 → UInt8 → Prop) (· < · : UInt8 → UInt8 → Prop) (· < ·) where
  trans := UInt8.lt_of_le_of_lt

-- abbrev UInt8.maxValue : UInt8 := 0xFF

-- @[simp] theorem UInt8.toBitVec_maxValue : UInt8.maxValue.toBitVec = BitVec.allOnes _ := rfl

-- @[simp] theorem UInt8.and_maxValue {b : UInt8} : b &&& UInt8.maxValue = b :=
--   UInt8.eq_of_toBitVec_eq (by rw [UInt8.toBitVec_and, toBitVec_maxValue, BitVec.and_allOnes])

theorem BitVec.and_or_distrib_left {a b c : BitVec w} : a &&& (b ||| c) = (a &&& b) ||| (a &&& c) :=
  BitVec.eq_of_getElem_eq (by simp [Bool.and_or_distrib_left])

theorem UInt8.add_or_distrib_left {a b c : UInt8} : a &&& (b ||| c) = (a &&& b) ||| (a &&& c) :=
  UInt8.eq_of_toBitVec_eq (by simp [BitVec.and_or_distrib_left])

  -- UInt8.eq_of_toBitVec_eq (by simp)


theorem UInt8.le_of_and_not_eq_zero {b c : UInt8} (h : b &&& ~~~c = 0) : b ≤ c :=
  calc
    b = b &&& (c ||| ~~~c) := by simp
    _ = b &&& c := by simp only [UInt8.add_or_distrib_left, h, UInt8.or_zero]
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
  if h : b &&& 0x80 == 0 then
    .done b (UInt8.lt_0x80_of_and_eq_zero (by simpa using h))
  else if b &&& 0xe0 == 0xc0 then
    .oneMore (b &&& 0x1f) (UInt8.and_lt_add_one (by decide))
  else if b &&& 0xf0 == 0xe0 then
    .twoMore (b &&& 0x0f) (UInt8.and_lt_add_one (by decide))
  else if b &&& 0xf8 == 0xf0 then
    .threeMore (b &&& 0x07) (UInt8.and_lt_add_one (by decide))
  else .invalid

#check Nat.isValidChar

def utf8DecodeChar? (bytes : ByteArray) (i : Nat) : Option Char :=
  if h₀ : i < bytes.size then
    match parseFirstByte bytes[i] with
    | .invalid => none
    | .done b₀ hb₀ => some ⟨b₀.toUInt32, Or.inl (by simp [UInt8.lt_iff_toNat_lt] at *; omega)⟩
    | .oneMore b₀ hb₀ =>
      if h₁ : i + 1 < bytes.size then
        let c₁ := bytes[i + 1]
        sorry
      else none
    | .twoMore b₀ hb₀ =>
      if h₁ : i + 2 < bytes.size then
        let c₁ := bytes[i + 1]
        let c₂ := bytes[i + 2]
        sorry
      else none
    | .threeMore b₀ hb₀ =>
      if h₁ : i + 3 < bytes.size then
        let c₁ := bytes[i + 1]
        let c₂ := bytes[i + 2]
        let c₃ := bytes[i + 3]
        sorry
      else none
  else none

-- def utf8DecodeChar? (bytes : ByteArray) (i : Nat) : Option Char :=
--   if h : i < bytes.size then
--     let c0 := bytes[i]
--     if c &&& 0x80 == 0 then
--       -- One byte encoding
--       sorry
--     else
--   else none


end decode
