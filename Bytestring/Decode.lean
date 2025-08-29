import Bytestring.ByteArray

/-! # `List` lemmas -/

theorem List.eq_getElem_of_length_eq_one : (l : List α) → (hl : l.length = 1) → l = [l[0]]
  | [_], _ => rfl

theorem List.eq_getElem_of_length_eq_two : (l : List α) → (hl : l.length = 2) → l = [l[0], l[1]]
  | [_, _], _ => rfl

theorem List.eq_getElem_of_length_eq_three : (l : List α) → (hl : l.length = 3) → l = [l[0], l[1], l[2]]
  | [_, _, _], _ => rfl

theorem List.eq_getElem_of_length_eq_four : (l : List α) → (hl : l.length = 4) → l = [l[0], l[1], l[2], l[3]  ]
  | [_, _, _, _], _ => rfl

/-! # `BitVec` lemmas -/

theorem BitVec.and_or_distrib_left {a b c : BitVec w} : a &&& (b ||| c) = (a &&& b) ||| (a &&& c) :=
  BitVec.eq_of_getElem_eq (by simp [Bool.and_or_distrib_left])

theorem BitVec.and_or_distrib_right {a b c : BitVec w} : (a ||| b) &&& c = (a &&& c) ||| (b &&& c) :=
  BitVec.eq_of_getElem_eq (by simp [Bool.and_or_distrib_right])

theorem BitVec.extractLsb'_setWidth_of_le {b : BitVec w} {start len w' : Nat} (h : start + len ≤ w') :
    (b.setWidth w').extractLsb' start len = b.extractLsb' start len := by
  ext i h_i
  simp
  omega

theorem BitVec.extractLsb'_append_eq_left {a : BitVec w} {b : BitVec w'} : (a ++ b).extractLsb' w' w = a := by
  simp [BitVec.extractLsb'_append_eq_of_le]

theorem BitVec.extractLsb'_append_eq_right {a : BitVec w} {b : BitVec w'} : (a ++ b).extractLsb' 0 w' = b := by
  simp [BitVec.extractLsb'_append_eq_of_add_le]

theorem BitVec.setWidth_append_eq_right {a : BitVec w} {b : BitVec w'} : (a ++ b).setWidth w' = b := by
  ext i hi
  simp [getLsbD_append, hi]

theorem BitVec.setWidth_setWidth_eq_self {a : BitVec w} {w' : Nat} (h : a < BitVec.twoPow w w') : (a.setWidth w').setWidth w = a := by
  by_cases hw : w' < w
  · simp only [toNat_eq, toNat_setWidth]
    rw [Nat.mod_mod_of_dvd' (Nat.pow_dvd_pow _ (Nat.le_of_lt hw)), Nat.mod_eq_of_lt]
    rwa [BitVec.lt_def, BitVec.toNat_twoPow_of_lt hw] at h
  · rw [BitVec.lt_def, BitVec.toNat_twoPow_of_le (by omega)] at h
    simp at h

theorem BitVec.append_left_inj {s₁ s₂ : BitVec w} (t : BitVec w') : s₁ ++ t = s₂ ++ t ↔ s₁ = s₂ := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  ext i hi
  simpa [getElem_append, dif_neg] using congrArg (·[i + w']'(by omega)) h

theorem BitVec.append_right_inj (s : BitVec w) {t₁ t₂ : BitVec w'} : s ++ t₁ = s ++ t₂ ↔ t₁ = t₂ := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  ext i hi
  simpa [getElem_append, hi] using congrArg (·[i]) h

theorem BitVec.cast_extractLsb' {x : BitVec w} {start len₁ len₂ : Nat} (h : len₁ = len₂) :
    (x.extractLsb' start len₁).cast h = x.extractLsb' start len₂ := by
  cases h; simp

theorem extractLsb'_append_extractLsb'_eq_extractLsb'_better {x : BitVec w} (h : start₂ = start₁ + len₁) :
    ((x.extractLsb' start₂ len₂) ++ (x.extractLsb' start₁ len₁)) =
    (x.extractLsb' start₁ (len₂ + len₁)) := by
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' h, BitVec.cast_extractLsb']

theorem BitVec.and_setWidth_allOnes (w' w : Nat) (b : BitVec (w' + w)) :
    b &&& (BitVec.allOnes w).setWidth (w' + w) = 0#w' ++ b.setWidth w := by
  ext i hi
  simp only [getElem_and, getElem_setWidth, getLsbD_allOnes]
  rw [BitVec.getElem_append]
  split <;> simp_all

theorem BitVec.setWidth_shiftRight {b : BitVec w} : (b >>> w').setWidth w'' = b.extractLsb' w' w'' := by
  ext i hi
  simp

theorem BitVec.setWidth_extractLsb'_of_le {c : BitVec w} (h : len₁ ≤ len₂) :
    (c.extractLsb' start len₂).setWidth len₁ = c.extractLsb' start len₁ := by
  ext i hi
  simp [show i < len₂ by omega]

theorem BitVec.length_pos_of_lt {b b' : BitVec w} (h : b < b') : 0 < w :=
  length_pos_of_ne (BitVec.ne_of_lt h)

theorem BitVec.not_lt_iff {b : BitVec w} : ~~~b < b ↔ 0 < w ∧ b.msb = true := by
  refine ⟨fun h => ?_, fun ⟨hw, hb⟩ => ?_⟩
  · have := length_pos_of_lt h
    exact ⟨this, by rwa [← ult_iff_lt, ult_eq_msb_of_msb_neq (by simp_all)] at h⟩
  · rwa [← ult_iff_lt, ult_eq_msb_of_msb_neq (by simp_all)]

theorem BitVec.setWidth_append_eq_shiftLeft_setWidth_or {b : BitVec w} {b' : BitVec w'} :
    (b ++ b').setWidth w'' = (b.setWidth w'' <<< w') ||| b'.setWidth w'' := by
  ext i hi
  simp only [getElem_setWidth, getElem_or, getElem_shiftLeft]
  rw [getLsbD_append]
  split <;> simp_all

theorem BitVec.setWidth_append_append_eq_shiftLeft_setWidth_or {b : BitVec w} {b' : BitVec w'} {b'' : BitVec w''} :
    (b ++ b' ++ b'').setWidth w''' = (b.setWidth w''' <<< (w' + w'')) ||| (b'.setWidth w''' <<< w'') ||| b''.setWidth w''' := by
  rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or,
    BitVec.setWidth_append_eq_shiftLeft_setWidth_or,
    BitVec.shiftLeft_or_distrib, BitVec.shiftLeft_add]

theorem BitVec.setWidth_append_append_append_eq_shiftLeft_setWidth_or {b : BitVec w} {b' : BitVec w'} {b'' : BitVec w''} {b''' : BitVec w'''} :
    (b ++ b' ++ b'' ++ b''').setWidth w'''' = (b.setWidth w'''' <<< (w' + w'' + w''')) ||| (b'.setWidth w'''' <<< (w'' + w''')) |||
      (b''.setWidth w'''' <<< w''') ||| b'''.setWidth w'''' := by
  simp only [BitVec.setWidth_append_eq_shiftLeft_setWidth_or, BitVec.shiftLeft_or_distrib, BitVec.shiftLeft_add]

theorem BitVec.toNat_setWidth_of_le {w w' : Nat} {b : BitVec w} (h : w ≤ w') : (b.setWidth w').toNat = b.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
  exact BitVec.toNat_lt_twoPow_of_le h

/-! # `UInt8` lemmas -/

instance : Trans (· ≤ · : UInt8 → UInt8 → Prop) (· < · : UInt8 → UInt8 → Prop) (· < ·) where
  trans := UInt8.lt_of_le_of_lt

theorem UInt8.and_or_distrib_left {a b c : UInt8} : a &&& (b ||| c) = (a &&& b) ||| (a &&& c) :=
  UInt8.eq_of_toBitVec_eq (by simp [BitVec.and_or_distrib_left])

theorem UInt8.and_or_distrib_right {a b c : UInt8} : (a ||| b) &&& c = (a &&& c) ||| (b &&& c) :=
  UInt8.eq_of_toBitVec_eq (by simp [BitVec.and_or_distrib_right])

theorem UInt8.le_of_and_not_eq_zero {b c : UInt8} (h : b &&& ~~~c = 0) : b ≤ c :=
  calc
    b = b &&& (c ||| ~~~c) := by simp
    _ = b &&& c := by simp only [UInt8.and_or_distrib_left, h, UInt8.or_zero]
    _ ≤ c := and_le_right

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

section decode

/-! # `parseFirstByte` -/

/-! ## `parseFirstByte` definition -/

inductive FirstByte where
  | invalid : FirstByte
  | done : FirstByte
  | oneMore : FirstByte
  | twoMore : FirstByte
  | threeMore : FirstByte

@[inline]
def parseFirstByte (b : UInt8) : FirstByte :=
  if b &&& 0x80 == 0 then
    .done
  else if b &&& 0xe0 == 0xc0 then
    .oneMore
  else if b &&& 0xf0 == 0xe0 then
    .twoMore
  else if b &&& 0xf8 == 0xf0 then
    .threeMore
  else .invalid

/-! ## `parseFirstByte` low-level API -/

theorem parseFirstByte_eq_done_iff : parseFirstByte b = .done ↔ b &&& 0x80 = 0 := by
  grind [parseFirstByte]

theorem parseFirstByte_eq_oneMore_iff : parseFirstByte b = .oneMore ↔ b &&& 0xe0 = 0xc0 := by
  suffices b &&& 0xe0 = 0xc0 → b &&& 0x80 ≠ 0 by grind [parseFirstByte]
  intro h
  calc b &&& 0x80 = b &&& (0xe0 &&& 0x80) := rfl
    _ = 0xc0 &&& 0x80 := by rw [← UInt8.and_assoc, h]
    _ ≠ 0 := by decide

theorem parseFirstByte_eq_twoMore_iff : parseFirstByte b = .twoMore ↔ b &&& 0xf0 = 0xe0 := by
  suffices b &&& 0xf0 = 0xe0 → b &&& 0xe0 ≠ 0xc0 ∧ b &&& 0x80 ≠ 0 by grind [parseFirstByte]
  refine fun h => ⟨?_, ?_⟩
  · calc b &&& 0xe0 = b &&& (0xf0 &&& 0xe0) := rfl
      _ = 0xe0 &&& 0xe0 := by rw [← UInt8.and_assoc, h]
      _ ≠ 0xc0 := by decide
  · calc b &&& 0x80 = b &&& (0xf0 &&& 0x80) := rfl
      _ = 0xe0 &&& 0x80 := by rw [← UInt8.and_assoc, h]
      _ ≠ 0 := by decide

theorem parseFirstByte_eq_threeMore_iff : parseFirstByte b = .threeMore ↔ b &&& 0xf8 = 0xf0 := by
  suffices b &&& 0xf8 = 0xf0 → b &&& 0xf0 ≠ 0xe0 ∧ b &&& 0xe0 ≠ 0xc0 ∧ b &&& 0x80 ≠ 0 by grind [parseFirstByte]
  refine fun h => ⟨?_, ?_, ?_⟩
  · calc b &&& 0xf0 = b &&& (0xf8 &&& 0xf0) := rfl
      _ = 0xf0 &&& 0xf0 := by rw [← UInt8.and_assoc, h]
      _ ≠ 0xe0 := by decide
  · calc b &&& 0xe0 = b &&& (0xf8 &&& 0xe0) := rfl
      _ = 0xf0 &&& 0xe0 := by rw [← UInt8.and_assoc, h]
      _ ≠ 0xc0 := by decide
  · calc b &&& 0x80 = b &&& (0xf8 &&& 0x80) := rfl
      _ = 0xf0 &&& 0x80 := by rw [← UInt8.and_assoc, h]
      _ ≠ 0 := by decide

/-! ## `parseFirstByte` BitVec API -/

theorem helper (w : Nat) (b : BitVec (w' + w)) (v : BitVec w') : b &&& (BitVec.allOnes w' ++ 0#w) = v ++ 0#w ↔ b.extractLsb' w w' = v := by
  have h : b = b.extractLsb' w w' ++ b.extractLsb' 0 w := by
    rw [extractLsb'_append_extractLsb'_eq_extractLsb'_better] <;> simp
  conv => lhs; rw [h]
  rw [BitVec.and_append, BitVec.and_allOnes, BitVec.and_zero, BitVec.append_left_inj]

theorem helper₂ (w : Nat) (b : BitVec (w' + w)) {v : BitVec w'} (h : b.extractLsb' w w' = v) : b = v ++ b.extractLsb' 0 w := by
  rw [← h, extractLsb'_append_extractLsb'_eq_extractLsb'_better] <;> simp

/-! ### Size one -/

theorem parseFirstByte_eq_done_iff_toBitVec : parseFirstByte b = .done ↔ b.toBitVec.extractLsb' 7 1 = 0#1 := by
  simp only [parseFirstByte_eq_done_iff, ← UInt8.toBitVec_inj, UInt8.toBitVec_and,
    UInt8.toBitVec_ofNat]
  exact helper 7 b.toBitVec 0#1

theorem toBitVec_eq_of_parseFirstByte_eq_done {b : UInt8} (h : parseFirstByte b = .done) :
    b.toBitVec = 0#1 ++ b.toBitVec.setWidth 7 := by
  exact helper₂ 7 b.toBitVec (parseFirstByte_eq_done_iff_toBitVec.1 h)

/-! ### Size two -/

theorem parseFirstByte_eq_oneMore_iff_toBitVec : parseFirstByte b = .oneMore ↔ b.toBitVec.extractLsb' 5 3 = 0b110#3 := by
  simp only [parseFirstByte_eq_oneMore_iff, ← UInt8.toBitVec_inj, UInt8.toBitVec_and,
    UInt8.toBitVec_ofNat]
  exact helper 5 b.toBitVec 0b110#3

theorem toBitVec_eq_of_parseFirstByte_eq_oneMore {b : UInt8} (h : parseFirstByte b = .oneMore) :
    b.toBitVec = 0b110#3 ++ b.toBitVec.setWidth 5 := by
  exact helper₂ 5 b.toBitVec (parseFirstByte_eq_oneMore_iff_toBitVec.1 h)

/-! ### Size three -/

theorem parseFirstByte_eq_twoMore_iff_toBitVec : parseFirstByte b = .twoMore ↔ b.toBitVec.extractLsb' 4 4 = 0b1110#4 := by
  simp only [parseFirstByte_eq_twoMore_iff, ← UInt8.toBitVec_inj, UInt8.toBitVec_and,
    UInt8.toBitVec_ofNat]
  exact helper 4 b.toBitVec 0b1110#4

theorem toBitVec_eq_of_parseFirstByte_eq_twoMore {b : UInt8} (h : parseFirstByte b = .twoMore) :
    b.toBitVec = 0b1110#4 ++ b.toBitVec.setWidth 4 := by
  exact helper₂ 4 b.toBitVec (parseFirstByte_eq_twoMore_iff_toBitVec.1 h)

/-! ### Size four -/

theorem parseFirstByte_eq_threeMore_iff_toBitVec : parseFirstByte b = .threeMore ↔ b.toBitVec.extractLsb' 3 5 = 0b11110#5 := by
  simp only [parseFirstByte_eq_threeMore_iff, ← UInt8.toBitVec_inj, UInt8.toBitVec_and,
    UInt8.toBitVec_ofNat]
  exact helper 3 b.toBitVec 0b11110#5

theorem toBitVec_eq_of_parseFirstByte_eq_threeMore {b : UInt8} (h : parseFirstByte b = .threeMore) :
    b.toBitVec = 0b11110#5 ++ b.toBitVec.setWidth 3 := by
  exact helper₂ 3 b.toBitVec (parseFirstByte_eq_threeMore_iff_toBitVec.1 h)

/-! # `isInvalidContinuationByte` definiton & API -/

@[inline]
def isInvalidContinuationByte (b : UInt8) : Bool :=
  b &&& 0xc0 != 0x80

theorem isInvalidContinutationByte_eq_false_iff {b : UInt8} :
    isInvalidContinuationByte b = false ↔ b &&& 0xc0 = 0x80 := by
  simp [isInvalidContinuationByte]

theorem isInvalidContinuationByte_eq_false_iff_toBitVec {b : UInt8} :
    isInvalidContinuationByte b = false ↔ b.toBitVec.extractLsb' 6 2 = 0b10#2 := by
  simp only [isInvalidContinuationByte, bne_eq_false_iff_eq, ← UInt8.toBitVec_inj,
    UInt8.toBitVec_and, UInt8.toBitVec_ofNat]
  exact helper 6 b.toBitVec 0b10#2

theorem toBitVec_eq_of_isInvalidContinuationByte_eq_false {b : UInt8} (hb : isInvalidContinuationByte b = false) :
    b.toBitVec = 0b10#2 ++ b.toBitVec.setWidth 6 := by
  exact helper₂ 6 b.toBitVec (isInvalidContinuationByte_eq_false_iff_toBitVec.1 hb)

/-! # `Char.utf8Size` -/

theorem Char.utf8Size_eq_one_iff {c : Char} : c.utf8Size = 1 ↔ c.val ≤ 127 := by
  grind [utf8Size]

theorem Char.utf8Size_eq_two_iff {c : Char} : c.utf8Size = 2 ↔ 128 ≤ c.val ∧ c.val ≤ 0x7ff := by
  grind [utf8Size]

theorem Char.utf8Size_eq_three_iff {c : Char} : c.utf8Size = 3 ↔ 0x7ff < c.val ∧ c.val ≤ 0xffff := by
  grind [utf8Size]

theorem Char.utf8Size_eq_four_iff {c : Char} : c.utf8Size = 4 ↔ 0xffff < c.val := by
  grind [utf8Size]

/-! # `utf8EncodeChar` -/

/-! ## `utf8EncodeChar` low-level API -/

theorem String.utf8EncodeChar_eq_singleton {c : Char} (h : c.utf8Size = 1) :
    String.utf8EncodeChar c = [c.val.toUInt8] := by
  grind [utf8EncodeChar, length_utf8EncodeChar]

theorem String.utf8EncodeChar_eq_cons_cons {c : Char} (h : c.utf8Size = 2) :
    String.utf8EncodeChar c = [(c.val >>>  6).toUInt8 &&& 0x1f ||| 0xc0, c.val.toUInt8 &&& 0x3f ||| 0x80] := by
  grind [utf8EncodeChar, length_utf8EncodeChar]

theorem String.utf8EncodeChar_eq_cons_cons_cons {c : Char} (h : c.utf8Size = 3) :
    String.utf8EncodeChar c =
    [(c.val >>> 12).toUInt8 &&& 0x0f ||| 0xe0,
     (c.val >>>  6).toUInt8 &&& 0x3f ||| 0x80,
              c.val.toUInt8 &&& 0x3f ||| 0x80] := by
  grind [utf8EncodeChar, length_utf8EncodeChar]

theorem String.utf8EncodeChar_eq_cons_cons_cons_cons {c : Char} (hc : c.utf8Size = 4) :
    String.utf8EncodeChar c =
    [(c.val >>> 18).toUInt8 &&& 0x07 ||| 0xf0,
     (c.val >>> 12).toUInt8 &&& 0x3f ||| 0x80,
     (c.val >>>  6).toUInt8 &&& 0x3f ||| 0x80,
              c.val.toUInt8 &&& 0x3f ||| 0x80] := by
  grind [utf8EncodeChar, length_utf8EncodeChar]

/-! ## `utf8EncodeChar` BitVec API -/

theorem helper₄ (s : Nat) (c : BitVec w₀) (v : BitVec w') (w : Nat) :
    (c >>> s).setWidth (w' + w) &&& (BitVec.allOnes w).setWidth (w' + w) ||| v ++ 0#w = v ++ c.extractLsb' s w := by
  rw [BitVec.and_setWidth_allOnes, BitVec.or_append, BitVec.zero_or, BitVec.or_zero,
    BitVec.setWidth_shiftRight, BitVec.setWidth_extractLsb'_of_le (by simp)]

/-! ### Size one -/

-- TODO: possibly it makes sense to factor out this proof
theorem String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_one {c : Char} (h : c.utf8Size = 1) :
    ((String.utf8EncodeChar c)[0]'(by simp [h])).toBitVec = 0#1 ++ c.val.toBitVec.extractLsb' 0 7 := by
  have h₀ : c.val.toNat < 128 := by
    suffices c.val.toNat ≤ 127 by omega
    simpa [Char.utf8Size_eq_one_iff, UInt32.le_iff_toNat_le] using h
  have h₁ : c.val.toNat < 256 := by omega
  rw [← BitVec.toNat_inj, BitVec.toNat_append]
  simp [utf8EncodeChar_eq_singleton h, Nat.mod_eq_of_lt h₀, Nat.mod_eq_of_lt h₁]

theorem parseFirstByte_utf8EncodeChar_eq_done {c : Char} (hc : c.utf8Size = 1) :
    parseFirstByte ((String.utf8EncodeChar c)[0]'(by simp [Char.utf8Size_pos])) = .done := by
  rw [parseFirstByte_eq_done_iff_toBitVec, String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_one hc,
    BitVec.extractLsb'_append_eq_left]

/-! ### Size two -/

theorem String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_two {c : Char} (h : c.utf8Size = 2) :
    ((String.utf8EncodeChar c)[0]'(by simp [h])).toBitVec = 0b110#3 ++ c.val.toBitVec.extractLsb' 6 5 := by
  simpa [String.utf8EncodeChar_eq_cons_cons h] using helper₄ 6 c.val.toBitVec 6#3 5

theorem String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_two {c : Char} (h : c.utf8Size = 2) :
    ((String.utf8EncodeChar c)[1]'(by simp [h])).toBitVec = 0b10#2 ++ c.val.toBitVec.extractLsb' 0 6 := by
  simpa [String.utf8EncodeChar_eq_cons_cons h] using helper₄ 0 c.val.toBitVec 2#2 6

theorem parseFirstByte_utf8EncodeChar_eq_oneMore {c : Char} (hc : c.utf8Size = 2) :
    parseFirstByte ((String.utf8EncodeChar c)[0]'(by simp [Char.utf8Size_pos])) = .oneMore := by
  rw [parseFirstByte_eq_oneMore_iff_toBitVec, String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_two hc,
    BitVec.extractLsb'_append_eq_left]

theorem isInvalidContinuationByte_getElem_utf8EncodeChar_one_of_utf8Size_eq_two {c : Char} (hc : c.utf8Size = 2) :
    isInvalidContinuationByte ((String.utf8EncodeChar c)[1]'(by simp [String.length_utf8EncodeChar, hc])) = false := by
  rw [isInvalidContinuationByte_eq_false_iff_toBitVec, String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_two hc,
    BitVec.extractLsb'_append_eq_left]

/-! ### Size three -/

theorem String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_three {c : Char} (h : c.utf8Size = 3) :
    ((String.utf8EncodeChar c)[0]'(by simp [h])).toBitVec = 0b1110#4 ++ c.val.toBitVec.extractLsb' 12 4 := by
  simpa [String.utf8EncodeChar_eq_cons_cons_cons h] using helper₄ 12 c.val.toBitVec 0b1110#4 4

theorem String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_three {c : Char} (h : c.utf8Size = 3) :
    ((String.utf8EncodeChar c)[1]'(by simp [h])).toBitVec = 0b10#2 ++ c.val.toBitVec.extractLsb' 6 6 := by
  simpa [String.utf8EncodeChar_eq_cons_cons_cons h] using helper₄ 6 c.val.toBitVec 0b10#2 6

theorem String.toBitVec_getElem_utf8EncodeChar_two_of_utf8Size_eq_three {c : Char} (h : c.utf8Size = 3) :
    ((String.utf8EncodeChar c)[2]'(by simp [h])).toBitVec = 0b10#2 ++ c.val.toBitVec.extractLsb' 0 6 := by
  simpa [String.utf8EncodeChar_eq_cons_cons_cons h] using helper₄ 0 c.val.toBitVec 0b10#2 6

theorem parseFirstByte_utf8EncodeChar_eq_twoMore {c : Char} (hc : c.utf8Size = 3) :
    parseFirstByte ((String.utf8EncodeChar c)[0]'(by simp [Char.utf8Size_pos])) = .twoMore := by
  rw [parseFirstByte_eq_twoMore_iff_toBitVec, String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_three hc,
    BitVec.extractLsb'_append_eq_left]

theorem isInvalidContinuationByte_getElem_utf8EncodeChar_one_of_utf8Size_eq_three {c : Char} (hc : c.utf8Size = 3) :
    isInvalidContinuationByte ((String.utf8EncodeChar c)[1]'(by simp [String.length_utf8EncodeChar, hc])) = false := by
  rw [isInvalidContinuationByte_eq_false_iff_toBitVec, String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_three hc,
    BitVec.extractLsb'_append_eq_left]

theorem isInvalidContinuationByte_getElem_utf8EncodeChar_two_of_utf8Size_eq_three {c : Char} (hc : c.utf8Size = 3) :
    isInvalidContinuationByte ((String.utf8EncodeChar c)[2]'(by simp [String.length_utf8EncodeChar, hc])) = false := by
  rw [isInvalidContinuationByte_eq_false_iff_toBitVec, String.toBitVec_getElem_utf8EncodeChar_two_of_utf8Size_eq_three hc,
    BitVec.extractLsb'_append_eq_left]

/-! ### Size four -/

theorem String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_four {c : Char} (h : c.utf8Size = 4) :
    ((String.utf8EncodeChar c)[0]'(by simp [h])).toBitVec = 0b11110#5 ++ c.val.toBitVec.extractLsb' 18 3 := by
  simpa [String.utf8EncodeChar_eq_cons_cons_cons_cons h] using helper₄ 18 c.val.toBitVec 0b11110#5 3

theorem String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_four {c : Char} (h : c.utf8Size = 4) :
    ((String.utf8EncodeChar c)[1]'(by simp [h])).toBitVec = 0b10#2 ++ c.val.toBitVec.extractLsb' 12 6 := by
  simpa [String.utf8EncodeChar_eq_cons_cons_cons_cons h] using helper₄ 12 c.val.toBitVec 0b10#2 6

theorem String.toBitVec_getElem_utf8EncodeChar_two_of_utf8Size_eq_four {c : Char} (h : c.utf8Size = 4) :
    ((String.utf8EncodeChar c)[2]'(by simp [h])).toBitVec = 0b10#2 ++ c.val.toBitVec.extractLsb' 6 6 := by
  simpa [String.utf8EncodeChar_eq_cons_cons_cons_cons h] using helper₄ 6 c.val.toBitVec 0b10#2 6

theorem String.toBitVec_getElem_utf8EncodeChar_three_of_utf8Size_eq_four {c : Char} (h : c.utf8Size = 4) :
    ((String.utf8EncodeChar c)[3]'(by simp [h])).toBitVec = 0b10#2 ++ c.val.toBitVec.extractLsb' 0 6 := by
  simpa [String.utf8EncodeChar_eq_cons_cons_cons_cons h] using helper₄ 0 c.val.toBitVec 0b10#2 6

theorem parseFirstByte_utf8EncodeChar_eq_threeMore {c : Char} (hc : c.utf8Size = 4) :
    parseFirstByte ((String.utf8EncodeChar c)[0]'(by simp [Char.utf8Size_pos])) = .threeMore := by
  rw [parseFirstByte_eq_threeMore_iff_toBitVec, String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_four hc,
    BitVec.extractLsb'_append_eq_left]

theorem isInvalidContinuationByte_getElem_utf8EncodeChar_one_of_utf8Size_eq_four {c : Char} (hc : c.utf8Size = 4) :
    isInvalidContinuationByte ((String.utf8EncodeChar c)[1]'(by simp [String.length_utf8EncodeChar, hc])) = false := by
  rw [isInvalidContinuationByte_eq_false_iff_toBitVec, String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_four hc,
    BitVec.extractLsb'_append_eq_left]

theorem isInvalidContinuationByte_getElem_utf8EncodeChar_two_of_utf8Size_eq_four {c : Char} (hc : c.utf8Size = 4) :
    isInvalidContinuationByte ((String.utf8EncodeChar c)[2]'(by simp [String.length_utf8EncodeChar, hc])) = false := by
  rw [isInvalidContinuationByte_eq_false_iff_toBitVec, String.toBitVec_getElem_utf8EncodeChar_two_of_utf8Size_eq_four hc,
    BitVec.extractLsb'_append_eq_left]

theorem isInvalidContinuationByte_getElem_utf8EncodeChar_three_of_utf8Size_eq_four {c : Char} (hc : c.utf8Size = 4) :
    isInvalidContinuationByte ((String.utf8EncodeChar c)[3]'(by simp [String.length_utf8EncodeChar, hc])) = false := by
  rw [isInvalidContinuationByte_eq_false_iff_toBitVec, String.toBitVec_getElem_utf8EncodeChar_three_of_utf8Size_eq_four hc,
    BitVec.extractLsb'_append_eq_left]

/-! # `assemble₁` -/

theorem helper₅ {w : UInt8} (h : parseFirstByte w = .done) : w < 128 := by
  simp only [UInt8.lt_iff_toBitVec_lt, UInt8.toBitVec_ofNat]
  rw [toBitVec_eq_of_parseFirstByte_eq_done h]
  simp only [Nat.reduceAdd, BitVec.lt_def, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [BitVec.toNat_append]
  simpa using Nat.mod_lt _ (by decide)

@[inline]
def assemble₁ (w : UInt8) (h : parseFirstByte w = .done) : Option Char :=
  some ⟨w.toUInt32, ?done⟩
where finally
  case done =>
    have : w < 0x80 := helper₅ h
    refine Or.inl ?_
    simp only [UInt8.lt_iff_toNat_lt, UInt8.reduceToNat] at this
    simp only [UInt8.toNat_toUInt32]
    omega

theorem toBitVec_val_assemble₁ {w : UInt8} {h} {c : Char} : assemble₁ w h = some c → c.val.toBitVec = w.toBitVec.setWidth 32 := by
  simp only [assemble₁, Option.some.injEq]
  rintro rfl
  rfl

theorem val_assemble₁_le {w : UInt8} {h} {c : Char} (h' : assemble₁ w h = some c) : c.val ≤ 127 := by
  have := toBitVec_val_assemble₁ h'
  have hx := helper₅ h
  simp only [UInt8.lt_iff_toNat_lt, UInt8.reduceToNat] at hx
  rw [UInt32.le_iff_toBitVec_le, this, BitVec.le_def]
  simp only [BitVec.toNat_setWidth, UInt8.toNat_toBitVec, Nat.reducePow, UInt8.toNat_mod_uInt32Size,
    UInt32.toBitVec_ofNat, BitVec.toNat_ofNat, Nat.reduceMod]
  omega

theorem utf8Size_assemble₁ {w : UInt8} {c : Char} {h} (h : assemble₁ w h = some c) : c.utf8Size = 1 :=
  Char.utf8Size_eq_one_iff.2 (val_assemble₁_le h)

theorem assemble₁_eq_some_iff_utf8EncodeChar_eq {w : UInt8} {c : Char} :
    (∃ h : parseFirstByte w = .done, assemble₁ w h = some c) ↔ String.utf8EncodeChar c = [w] := by
  refine ⟨fun ⟨h₁, h₂⟩ => ?_, ?_⟩
  · have hc := utf8Size_assemble₁ h₂
    simp only [String.utf8EncodeChar_eq_singleton hc, List.cons.injEq, and_true]
    simp only [assemble₁, Option.some.injEq] at h₂
    simpa using congrArg (·.val.toUInt8) h₂ |>.symm
  · intro h
    have h₀ : (String.utf8EncodeChar c).length = 1 := congrArg List.length h
    have hc : c.utf8Size = 1 := String.length_utf8EncodeChar _ ▸ h₀
    obtain ⟨rfl⟩ : w = (String.utf8EncodeChar c)[0] := by simp [h]
    refine ⟨parseFirstByte_utf8EncodeChar_eq_done hc, ?_⟩
    have : c.val.toNat < 256 := by
      simp only [Char.utf8Size_eq_one_iff, UInt32.le_iff_toNat_le, UInt32.reduceToNat] at hc
      omega
    simpa [String.utf8EncodeChar_eq_singleton hc, assemble₁, Char.ext_iff, ← UInt32.toNat_inj]

/-! # `assemble₂` -/

@[inline]
def assemble₂Unchecked (w x : UInt8) : UInt32 :=
  let b₀ : UInt8 := w &&& 0x1f
  let b₁ := x &&& 0x3f
  (b₀.toUInt32 <<< 6) ||| b₁.toUInt32

@[inline]
def assemble₂ (w x : UInt8) : Option Char :=
  if isInvalidContinuationByte x then
    none
  else
    let r := assemble₂Unchecked w x
    if r < 0x80 then
      none -- overlong encodinlg
    else
      some ⟨r, ?onemore⟩
where finally
  case onemore =>
    let b₀ : UInt8 := w &&& 0x1f
    let b₁ := x &&& 0x3f
    have hr : r = (b₀.toUInt32 <<< 6) ||| b₁.toUInt32 := rfl
    have hb₀ : b₀ < 0x20 := UInt8.and_lt_add_one (by decide)
    have hb₁ : b₁ < 0x40 := UInt8.and_lt_add_one (by decide)
    refine Or.inl ?_
    simp only [UInt8.lt_iff_toNat_lt, UInt8.reduceToNat] at hb₀ hb₁
    simp only [hr, UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, UInt32.reduceToNat,
      Nat.reduceMod, Nat.reducePow]
    rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hb₁]
    omega

theorem helper₃ {x : UInt8} (n : Nat) (hn : n < 8) :
    (x &&& UInt8.ofNat (2 ^ n - 1)).toUInt32.toBitVec = (x.toBitVec.setWidth n).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [UInt8.toUInt32_and, UInt32.toBitVec_and, UInt8.toBitVec_toUInt32, BitVec.toNat_and,
    BitVec.toNat_setWidth, UInt8.toNat_toBitVec, Nat.reducePow, UInt8.toNat_mod_uInt32Size,
    UInt8.toNat_ofNat']
  have : 2 ^ n < 2 ^ 8 := Nat.pow_lt_pow_right (by decide) hn
  rw [Nat.mod_mod_of_dvd' (by decide), Nat.mod_eq_of_lt (by omega), Nat.mod_mod_of_dvd']
  · exact Nat.and_two_pow_sub_one_eq_mod _ _
  · exact Nat.pow_dvd_pow (n := 32) 2 (by omega)

theorem toBitVec_assemble₂Unchecked {w x : UInt8} : (assemble₂Unchecked w x).toBitVec = (w.toBitVec.setWidth 5 ++ x.toBitVec.setWidth 6).setWidth 32 := by
  have hw : (w &&& 31).toUInt32.toBitVec = (w.toBitVec.setWidth 5).setWidth 32 := helper₃ 5 (by decide)
  have hx : (x &&& 63).toUInt32.toBitVec = (x.toBitVec.setWidth 6).setWidth 32 := helper₃ 6 (by decide)
  rw [assemble₂Unchecked, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, hw, hx]
  simpa using BitVec.setWidth_append_eq_shiftLeft_setWidth_or.symm

theorem toBitVec_val_assemble₂ {w x : UInt8} (c : Char) : assemble₂ w x = some c → c.val.toBitVec = (w.toBitVec.setWidth 5 ++ x.toBitVec.setWidth 6).setWidth 32 := by
  fun_cases assemble₂ with
  | case1 => simp
  | case2 => simp
  | case3 hx r hr =>
    simp only [Option.some.injEq, Nat.reduceAdd]
    rintro rfl
    subst r
    simp [toBitVec_assemble₂Unchecked]

theorem le_val_assemble₂ {w x : UInt8} {c : Char} : assemble₂ w x = some c → 128 ≤ c.val := by
  rcases c with ⟨v, hv⟩
  fun_cases assemble₂ with
  | case1 => simp
  | case2 => simp
  | case3 hx r hr =>
    simp only [Option.some.injEq, Char.mk.injEq]
    rintro rfl
    exact UInt32.not_lt.1 hr

theorem val_assemble₂_le {w x : UInt8} {c : Char} (h : assemble₂ w x = some c) : c.val ≤ 2047 := by
  rw [UInt32.le_iff_toBitVec_le, toBitVec_val_assemble₂ _ h, BitVec.le_def, BitVec.toNat_setWidth_of_le (by simp)]
  exact Nat.le_of_lt_succ (BitVec.toNat_lt_twoPow_of_le (Nat.le_refl _))

theorem utf8Size_assemble₂ {w x : UInt8} {c : Char} (h : assemble₂ w x = some c) : c.utf8Size = 2 :=
  Char.utf8Size_eq_two_iff.2 ⟨le_val_assemble₂ h, val_assemble₂_le h⟩

theorem helper₆ {c : Char} {o : Option Char} {b : BitVec 32} (hc : c.val.toBitVec = b) (h' : ∀ d, o = some d → d.val.toBitVec = b)
    (hi : o.isSome) : o = some c := by
  obtain rfl : c = o.get hi := by
    refine Char.ext (UInt32.eq_of_toBitVec_eq ?_)
    rw [hc, h' (o.get hi) (by simp)]
  simp

theorem assemble₂_eq_some_of_toBitVec {w x : UInt8} (hx : isInvalidContinuationByte x = false) {c : Char} (hc₀ : 128 ≤ c.val)
    (hc : c.val.toBitVec = (w.toBitVec.setWidth 5 ++ x.toBitVec.setWidth 6).setWidth 32) : assemble₂ w x = some c := by
  apply helper₆ hc toBitVec_val_assemble₂
  fun_cases assemble₂ with
  | case1 => simp_all
  | case2 hx r hr =>
    suffices 128 ≤ r.toNat ∧ r.toNat < 128 by omega
    simp_all [← toBitVec_assemble₂Unchecked, r, UInt32.le_iff_toBitVec_le, UInt32.lt_iff_toBitVec_lt, BitVec.le_def, BitVec.lt_def]
  | case3 hx r hr => simp

theorem isInvalidContinuationByte_eq_false_of_assemble₂_eq_some {w x : UInt8} {c : Char} : assemble₂ w x = some c → isInvalidContinuationByte x = false := by
  grind [assemble₂]

theorem assemble₂_eq_some_iff_utf8EncodeChar_eq {x y : UInt8} {c : Char} :
    parseFirstByte x = .oneMore ∧ assemble₂ x y = some c ↔ String.utf8EncodeChar c = [x, y] := by
  refine ⟨fun ⟨h₁, h₂⟩ => ?_, ?_⟩
  · have hc := utf8Size_assemble₂ h₂
    rw [(String.utf8EncodeChar c).eq_getElem_of_length_eq_two (by simp [hc])]
    simp only [List.cons.injEq, and_true, UInt8.eq_iff_toBitVec_eq]
    refine ⟨?_, ?_⟩
    · rw [String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_two hc,
        toBitVec_val_assemble₂ _ h₂, BitVec.extractLsb'_setWidth_of_le (by decide),
        BitVec.extractLsb'_append_eq_left]
      conv => rhs; rw [toBitVec_eq_of_parseFirstByte_eq_oneMore h₁]
    · rw [String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_two hc,
        toBitVec_val_assemble₂ _ h₂]
      rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
      conv => rhs; rw [toBitVec_eq_of_isInvalidContinuationByte_eq_false (isInvalidContinuationByte_eq_false_of_assemble₂_eq_some h₂)]
      rw [BitVec.extractLsb'_append_eq_right]
  · intro h
    have hc : c.utf8Size = 2 := String.length_utf8EncodeChar _ ▸ congrArg List.length h
    have h₀ : (String.utf8EncodeChar c).length = 2 := congrArg List.length h
    obtain ⟨rfl, rfl⟩ : x = (String.utf8EncodeChar c)[0] ∧ y = (String.utf8EncodeChar c)[1] := by simp [h]
    refine ⟨parseFirstByte_utf8EncodeChar_eq_oneMore hc, ?_⟩
    apply assemble₂_eq_some_of_toBitVec
    · apply isInvalidContinuationByte_getElem_utf8EncodeChar_one_of_utf8Size_eq_two hc
    · rw [Char.utf8Size_eq_two_iff] at hc
      exact hc.1
    · rw [String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_two hc,
        String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_two hc,
        BitVec.setWidth_append_eq_right, BitVec.setWidth_append_eq_right,
        extractLsb'_append_extractLsb'_eq_extractLsb'_better (by simp),
        ← BitVec.setWidth_eq_extractLsb' (by simp),
        BitVec.setWidth_setWidth_eq_self]
      simpa [BitVec.lt_def, UInt32.le_iff_toNat_le] using Nat.lt_succ_iff.2 (Char.utf8Size_eq_two_iff.1 hc).2

/-! # `assemble₃` -/

@[inline]
def assemble₃Unchecked (w x y : UInt8) : UInt32 :=
  let b₀ : UInt8 := w &&& 0x0f
  let b₁ := x &&& 0x3f
  let b₂ := y &&& 0x3f
  (b₀.toUInt32 <<< 12) ||| (b₁.toUInt32 <<< 6) ||| b₂.toUInt32

@[inline]
def assemble₃ (w x y : UInt8) : Option Char :=
  if isInvalidContinuationByte x || isInvalidContinuationByte y then
    none
  else
    let r := assemble₃Unchecked w x y
    if r < 0x800 then
      none -- overlong encoding
    else if hr : 0xd800 ≤ r ∧ r ≤ 0xdfff then
      none -- surrogate code point
    else
      some ⟨r, ?twomore⟩
where finally
  case twomore =>
    let b₀ : UInt8 := w &&& 0x0f
    let b₁ := x &&& 0x3f
    let b₂ := y &&& 0x3f
    have hb₀ : b₀ < 0x10 := UInt8.and_lt_add_one (by decide)
    have hb₁ : b₁ < 0x40 := UInt8.and_lt_add_one (by decide)
    have hb₂ : b₂ < 0x40 := UInt8.and_lt_add_one (by decide)
    have hr' : r = (b₀.toUInt32 <<< 12) ||| (b₁.toUInt32 <<< 6) ||| b₂.toUInt32 := rfl
    simp only [UInt8.lt_iff_toNat_lt, UInt8.reduceToNat] at hb₀ hb₁ hb₂
    simp only [Decidable.not_and_iff_not_or_not, UInt32.not_le] at hr
    rcases hr with (hr|hr)
    · exact Or.inl hr
    · refine Or.inr ⟨hr, ?_⟩
      subst r
      simp only [hr', UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, UInt32.reduceToNat,
        Nat.reduceMod, Nat.reducePow]
      rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mul_comm _ (2 ^ _), Nat.mul_comm _ (2 ^ _), Nat.or_assoc, ← Nat.two_pow_add_eq_or_of_lt (b := b₂.toNat) hb₂,
          ← Nat.two_pow_add_eq_or_of_lt (by omega)]
      omega

theorem toBitVec_assemble₃Unchecked {w x y : UInt8} : (assemble₃Unchecked w x y).toBitVec =
    (w.toBitVec.setWidth 4 ++ x.toBitVec.setWidth 6 ++ y.toBitVec.setWidth 6).setWidth 32 := by
  have hw : (w &&& 15).toUInt32.toBitVec = (w.toBitVec.setWidth 4).setWidth 32 := helper₃ 4 (by decide)
  have hx : (x &&& 63).toUInt32.toBitVec = (x.toBitVec.setWidth 6).setWidth 32 := helper₃ 6 (by decide)
  have hy : (y &&& 63).toUInt32.toBitVec = (y.toBitVec.setWidth 6).setWidth 32 := helper₃ 6 (by decide)
  rw [assemble₃Unchecked, UInt32.toBitVec_or, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftLeft,
    hw, hx, hy, BitVec.setWidth_append_append_eq_shiftLeft_setWidth_or]
  simp

theorem toBitVec_val_assemble₃ {w x y : UInt8} (c : Char) : assemble₃ w x y = some c →
    c.val.toBitVec = (w.toBitVec.setWidth 4 ++ x.toBitVec.setWidth 6 ++ y.toBitVec.setWidth 6).setWidth 32 := by
  fun_cases assemble₃ with
  | case1 => simp
  | case2 => simp
  | case3 => simp
  | case4 hx r hr =>
    simp only [Option.some.injEq, Nat.reduceAdd]
    rintro rfl
    subst r
    simp [toBitVec_assemble₃Unchecked]

theorem le_val_assemble₃ {w x y : UInt8} {c : Char} : assemble₃ w x y = some c → 0x800 ≤ c.val := by
  rcases c with ⟨v, hv⟩
  fun_cases assemble₃ with
  | case1 => simp
  | case2 => simp
  | case3 => simp
  | case4 hx r hr =>
    simp only [Option.some.injEq, Char.mk.injEq]
    rintro rfl
    exact UInt32.not_lt.1 hr

theorem val_assemble₃_le {w x y : UInt8} {c : Char} (h : assemble₃ w x y = some c) : c.val ≤ 0xffff := by
  rw [UInt32.le_iff_toBitVec_le, toBitVec_val_assemble₃ _ h, BitVec.le_def, BitVec.toNat_setWidth_of_le (by simp)]
  exact Nat.le_of_lt_succ (BitVec.toNat_lt_twoPow_of_le (Nat.le_refl _))

theorem utf8Size_assemble₃ {w x y : UInt8} {c : Char} (h : assemble₃ w x y = some c) : c.utf8Size = 3 :=
  Char.utf8Size_eq_three_iff.2 ⟨le_val_assemble₃ h, val_assemble₃_le h⟩

theorem assemble₃_eq_some_of_toBitVec {w x y : UInt8} (hx : isInvalidContinuationByte x = false)
    (hy : isInvalidContinuationByte y = false) {c : Char} (hc₀ : 0x800 ≤ c.val)
    (hc : c.val.toBitVec = (w.toBitVec.setWidth 4 ++ x.toBitVec.setWidth 6 ++ y.toBitVec.setWidth 6).setWidth 32) :
    assemble₃ w x y = some c := by
  apply helper₆ hc toBitVec_val_assemble₃
  fun_cases assemble₃ with
  | case1 => simp_all
  | case2 hx r hr =>
    suffices 0x800 ≤ (assemble₃Unchecked w x y).toNat ∧ (assemble₃Unchecked w x y).toNat < 0x800 by omega
    simp_all [← toBitVec_assemble₃Unchecked, r, UInt32.le_iff_toBitVec_le, UInt32.lt_iff_toBitVec_lt, BitVec.le_def, BitVec.lt_def]
  | case3 hx r hr hr' =>
    have hcv := c.valid
    suffices ((55296 ≤ r.toNat ∧ r.toNat ≤ 57343) ∧ (r.toNat < 55296 ∨ (57343 < r.toNat ∧ r.toNat < 1114112))) by omega
    simp_all [UInt32.isValidChar, Nat.isValidChar, ← toBitVec_assemble₃Unchecked, r, UInt32.le_iff_toBitVec_le, UInt32.lt_iff_toBitVec_lt,
      BitVec.le_def, BitVec.lt_def, ← BitVec.toNat_inj]
  | case4 => simp

theorem isInvalidContinuationByte_eq_false_of_assemble₃_eq_some_left {w x y : UInt8} {c : Char} : assemble₃ w x y = some c → isInvalidContinuationByte x = false := by
  grind [assemble₃]

theorem isInvalidContinuationByte_eq_false_of_assemble₃_eq_some_right {w x y : UInt8} {c : Char} : assemble₃ w x y = some c → isInvalidContinuationByte y = false := by
  grind [assemble₃]

theorem assemble₃_eq_some_iff_utf8EncodeChar_eq {w x y : UInt8} {c : Char} :
    parseFirstByte w = .twoMore ∧ assemble₃ w x y = some c ↔ String.utf8EncodeChar c = [w, x, y] := by
  refine ⟨fun ⟨h₁, h₂⟩ => ?_, ?_⟩
  · have hc := utf8Size_assemble₃ h₂
    rw [(String.utf8EncodeChar c).eq_getElem_of_length_eq_three (by simp [hc])]
    simp only [List.cons.injEq, UInt8.eq_iff_toBitVec_eq, and_true]
    refine ⟨?_, ?_, ?_⟩
    · rw [String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_three hc,
        toBitVec_val_assemble₃ _ h₂, BitVec.extractLsb'_setWidth_of_le (by decide),
        BitVec.append_assoc, BitVec.cast_eq, BitVec.extractLsb'_append_eq_left,
        ← toBitVec_eq_of_parseFirstByte_eq_twoMore h₁]
    · rw [String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_three hc,
        toBitVec_val_assemble₃ _ h₂, BitVec.extractLsb'_setWidth_of_le (by decide),
        BitVec.extractLsb'_append_eq_of_le (by decide), BitVec.extractLsb'_append_eq_right,
        ← toBitVec_eq_of_isInvalidContinuationByte_eq_false (isInvalidContinuationByte_eq_false_of_assemble₃_eq_some_left h₂)]
    · rw [String.toBitVec_getElem_utf8EncodeChar_two_of_utf8Size_eq_three hc,
        toBitVec_val_assemble₃ _ h₂, BitVec.extractLsb'_setWidth_of_le (by decide),
        BitVec.extractLsb'_append_eq_right,
        ← toBitVec_eq_of_isInvalidContinuationByte_eq_false (isInvalidContinuationByte_eq_false_of_assemble₃_eq_some_right h₂)]
  · intro h
    have h₀ : (String.utf8EncodeChar c).length = 3 := congrArg List.length h
    have hc : c.utf8Size = 3 := String.length_utf8EncodeChar _ ▸ h₀
    obtain ⟨rfl, rfl, rfl⟩ : w = (String.utf8EncodeChar c)[0] ∧ x = (String.utf8EncodeChar c)[1] ∧
      y = (String.utf8EncodeChar c)[2] := by simp [h]
    refine ⟨parseFirstByte_utf8EncodeChar_eq_twoMore hc, ?_⟩
    apply assemble₃_eq_some_of_toBitVec
    · apply isInvalidContinuationByte_getElem_utf8EncodeChar_one_of_utf8Size_eq_three hc
    · apply isInvalidContinuationByte_getElem_utf8EncodeChar_two_of_utf8Size_eq_three hc
    · simp [Char.utf8Size_eq_three_iff, UInt32.lt_iff_toNat_lt] at hc
      exact UInt32.le_iff_toNat_le.2 (by simp; omega)
    · rw [String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_three hc,
        String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_three hc,
        String.toBitVec_getElem_utf8EncodeChar_two_of_utf8Size_eq_three hc,
        BitVec.setWidth_append_eq_right, BitVec.setWidth_append_eq_right, BitVec.setWidth_append_eq_right,
        extractLsb'_append_extractLsb'_eq_extractLsb'_better (by simp),
        extractLsb'_append_extractLsb'_eq_extractLsb'_better (by simp),
        ← BitVec.setWidth_eq_extractLsb' (by simp), BitVec.setWidth_setWidth_eq_self]
      simpa [BitVec.lt_def, UInt32.le_iff_toNat_le] using Nat.lt_succ_iff.2 (Char.utf8Size_eq_three_iff.1 hc).2

/-! # `assemble₄` -/

@[inline]
def assemble₄Unchecked (w x y z : UInt8) : UInt32 :=
  let b₀ : UInt8 := w &&& 0x07
  let b₁ := x &&& 0x3f
  let b₂ := y &&& 0x3f
  let b₃ := z &&& 0x3f
  (b₀.toUInt32 <<< 18) ||| (b₁.toUInt32 <<< 12) ||| (b₂.toUInt32 <<< 6) ||| b₃.toUInt32

@[inline]
def assemble₄ (w x y z : UInt8) : Option Char :=
  if isInvalidContinuationByte x || isInvalidContinuationByte y || isInvalidContinuationByte z then
    none
  else
    let r := assemble₄Unchecked w x y z
    if h₁ : r < 0x10000 then
      none -- overlong encoding
    else if h₂ : 0x10ffff < r then
      none -- out-of-range code point
    else
      some ⟨r, ?threemore⟩
where finally
  case threemore =>
    simp only [UInt32.not_lt, UInt32.le_iff_toNat_le, UInt32.reduceToNat] at h₁ h₂
    exact Or.inr ⟨by omega, by omega⟩

theorem toBitVec_assemble₄Unchecked {w x y z : UInt8} : (assemble₄Unchecked w x y z).toBitVec =
    (w.toBitVec.setWidth 3 ++ x.toBitVec.setWidth 6 ++ y.toBitVec.setWidth 6 ++ z.toBitVec.setWidth 6).setWidth 32 := by
  have hw : (w &&& 7).toUInt32.toBitVec = (w.toBitVec.setWidth 3).setWidth 32 := helper₃ 3 (by decide)
  have hx : (x &&& 63).toUInt32.toBitVec = (x.toBitVec.setWidth 6).setWidth 32 := helper₃ 6 (by decide)
  have hy : (y &&& 63).toUInt32.toBitVec = (y.toBitVec.setWidth 6).setWidth 32 := helper₃ 6 (by decide)
  have hz : (z &&& 63).toUInt32.toBitVec = (z.toBitVec.setWidth 6).setWidth 32 := helper₃ 6 (by decide)
  rw [assemble₄Unchecked, UInt32.toBitVec_or, UInt32.toBitVec_or, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft,
    UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftLeft, hw, hx, hy, hz, BitVec.setWidth_append_append_append_eq_shiftLeft_setWidth_or]
  simp

theorem toBitVec_val_assemble₄ {w x y z : UInt8} (c : Char) : assemble₄ w x y z = some c →
    c.val.toBitVec = (w.toBitVec.setWidth 3 ++ x.toBitVec.setWidth 6 ++ y.toBitVec.setWidth 6 ++ z.toBitVec.setWidth 6).setWidth 32 := by
  fun_cases assemble₄ with
  | case1 => simp
  | case2 => simp
  | case3 => simp
  | case4 hx r hr =>
    simp only [Option.some.injEq, Nat.reduceAdd]
    rintro rfl
    subst r
    simp [toBitVec_assemble₄Unchecked]

theorem le_val_assemble₄ {w x y z : UInt8} {c : Char} : assemble₄ w x y z = some c → 0xffff < c.val := by
  rcases c with ⟨v, hv⟩
  fun_cases assemble₄ with
  | case1 => simp
  | case2 => simp
  | case3 => simp
  | case4 hx r hr =>
    simp only [Option.some.injEq, Char.mk.injEq]
    rintro rfl
    have := UInt32.not_lt.1 hr
    simp only [UInt32.le_iff_toNat_le, UInt32.reduceToNat] at this
    simp only [UInt32.lt_iff_toNat_lt, UInt32.reduceToNat, gt_iff_lt]
    omega

theorem utf8Size_assemble₄ {w x y z : UInt8} {c : Char} (h : assemble₄ w x y z = some c) : c.utf8Size = 4 :=
  Char.utf8Size_eq_four_iff.2 (le_val_assemble₄ h)

theorem assemble₄_eq_some_of_toBitVec {w x y z : UInt8} (hx : isInvalidContinuationByte x = false)
    (hy : isInvalidContinuationByte y = false) (hz : isInvalidContinuationByte z = false) {c : Char} (hc₀ : 0x10000 ≤ c.val)
    (hc : c.val.toBitVec = (w.toBitVec.setWidth 3 ++ x.toBitVec.setWidth 6 ++ y.toBitVec.setWidth 6 ++ z.toBitVec.setWidth 6).setWidth 32) :
    assemble₄ w x y z = some c := by
  apply helper₆ hc toBitVec_val_assemble₄
  fun_cases assemble₄ with
  | case1 => simp_all
  | case2 hx r hr =>
    suffices 0x10000 ≤ (assemble₄Unchecked w x y z).toNat ∧ (assemble₄Unchecked w x y z).toNat < 0x10000 by omega
    simp_all [← toBitVec_assemble₄Unchecked, r, UInt32.le_iff_toBitVec_le, UInt32.lt_iff_toBitVec_lt, BitVec.le_def, BitVec.lt_def]
  | case3 hx r hr hr' =>
    have hcv := c.valid
    suffices (1114111 < r.toNat ∧ (r.toNat < 55296 ∨ (57343 < r.toNat ∧ r.toNat < 1114112))) by omega
    simp_all [UInt32.isValidChar, Nat.isValidChar, ← toBitVec_assemble₄Unchecked, r, UInt32.le_iff_toBitVec_le, UInt32.lt_iff_toBitVec_lt,
      BitVec.le_def, BitVec.lt_def, ← BitVec.toNat_inj]
  | case4 => simp

theorem isInvalidContinuationByte_eq_false_of_assemble₄_eq_some_left {w x y z : UInt8} {c : Char} : assemble₄ w x y z = some c → isInvalidContinuationByte x = false := by
  grind [assemble₄]

theorem isInvalidContinuationByte_eq_false_of_assemble₄_eq_some_middle {w x y z : UInt8} {c : Char} : assemble₄ w x y z = some c → isInvalidContinuationByte y = false := by
  grind [assemble₄]

theorem isInvalidContinuationByte_eq_false_of_assemble₄_eq_some_right {w x y z : UInt8} {c : Char} : assemble₄ w x y z = some c → isInvalidContinuationByte z = false := by
  grind [assemble₄]

theorem Char.toNat_val_le {c : Char} : c.val.toNat ≤ 0x10ffff := by
  have := c.valid
  simp [UInt32.isValidChar, Nat.isValidChar] at this
  omega

theorem assemble₄_eq_some_iff_utf8EncodeChar_eq {w x y z : UInt8} {c : Char} :
    parseFirstByte w = .threeMore ∧ assemble₄ w x y z = some c ↔ String.utf8EncodeChar c = [w, x, y, z] := by
  refine ⟨fun ⟨h₁, h₂⟩ => ?_, ?_⟩
  · have hc := utf8Size_assemble₄ h₂
    rw [(String.utf8EncodeChar c).eq_getElem_of_length_eq_four (by simp [hc])]
    simp only [List.cons.injEq, UInt8.eq_iff_toBitVec_eq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_four hc,
        toBitVec_val_assemble₄ _ h₂, BitVec.extractLsb'_setWidth_of_le (by decide),
        BitVec.append_assoc, BitVec.cast_eq, BitVec.append_assoc, BitVec.cast_eq,
        BitVec.extractLsb'_append_eq_left,
        ← toBitVec_eq_of_parseFirstByte_eq_threeMore h₁]
    · rw [String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_four hc,
        toBitVec_val_assemble₄ _ h₂, BitVec.extractLsb'_setWidth_of_le (by decide),
        BitVec.extractLsb'_append_eq_of_le (by decide), BitVec.extractLsb'_append_eq_of_le (by decide),
        BitVec.extractLsb'_append_eq_right,
        ← toBitVec_eq_of_isInvalidContinuationByte_eq_false (isInvalidContinuationByte_eq_false_of_assemble₄_eq_some_left h₂)]
    · rw [String.toBitVec_getElem_utf8EncodeChar_two_of_utf8Size_eq_four hc,
        toBitVec_val_assemble₄ _ h₂, BitVec.extractLsb'_setWidth_of_le (by decide),
        BitVec.extractLsb'_append_eq_of_le (by decide), BitVec.extractLsb'_append_eq_right,
        ← toBitVec_eq_of_isInvalidContinuationByte_eq_false (isInvalidContinuationByte_eq_false_of_assemble₄_eq_some_middle h₂)]
    · rw [String.toBitVec_getElem_utf8EncodeChar_three_of_utf8Size_eq_four hc,
        toBitVec_val_assemble₄ _ h₂, BitVec.extractLsb'_setWidth_of_le (by decide),
        BitVec.extractLsb'_append_eq_right,
        ← toBitVec_eq_of_isInvalidContinuationByte_eq_false (isInvalidContinuationByte_eq_false_of_assemble₄_eq_some_right h₂)]
  · intro h
    have h₀ : (String.utf8EncodeChar c).length = 4 := congrArg List.length h
    have hc : c.utf8Size = 4 :=  String.length_utf8EncodeChar _ ▸ h₀
    obtain ⟨rfl, rfl, rfl, rfl⟩ :
      w = (String.utf8EncodeChar c)[0] ∧ x = (String.utf8EncodeChar c)[1] ∧ y = (String.utf8EncodeChar c)[2]
        ∧ z = (String.utf8EncodeChar c)[3] := by simp [h]
    refine ⟨parseFirstByte_utf8EncodeChar_eq_threeMore hc, ?_⟩
    apply assemble₄_eq_some_of_toBitVec
    · apply isInvalidContinuationByte_getElem_utf8EncodeChar_one_of_utf8Size_eq_four hc
    · apply isInvalidContinuationByte_getElem_utf8EncodeChar_two_of_utf8Size_eq_four hc
    · apply isInvalidContinuationByte_getElem_utf8EncodeChar_three_of_utf8Size_eq_four hc
    · simp [Char.utf8Size_eq_four_iff, UInt32.lt_iff_toNat_lt] at hc
      exact UInt32.le_iff_toNat_le.2 (by simp; omega)
    · rw [String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_four hc,
        String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_four hc,
        String.toBitVec_getElem_utf8EncodeChar_two_of_utf8Size_eq_four hc,
        String.toBitVec_getElem_utf8EncodeChar_three_of_utf8Size_eq_four hc,
        BitVec.setWidth_append_eq_right, BitVec.setWidth_append_eq_right, BitVec.setWidth_append_eq_right,
        BitVec.setWidth_append_eq_right,
        extractLsb'_append_extractLsb'_eq_extractLsb'_better (by simp),
        extractLsb'_append_extractLsb'_eq_extractLsb'_better (by simp),
        extractLsb'_append_extractLsb'_eq_extractLsb'_better (by simp),
        ← BitVec.setWidth_eq_extractLsb' (by simp), BitVec.setWidth_setWidth_eq_self]
      have := c.toNat_val_le
      simp only [Nat.reduceAdd, BitVec.lt_def, UInt32.toNat_toBitVec, BitVec.toNat_twoPow,
        Nat.reducePow, Nat.reduceMod, gt_iff_lt]
      omega

/- # `utf8DecodeChar?` -/

@[inline]
def utf8DecodeChar? (bytes : ByteArray) (i : Nat) : Option Char :=
  if h₀ : i < bytes.size then
    match h : parseFirstByte bytes[i] with
    | .invalid => none -- invalid first byte
    | .done => assemble₁ bytes[i] h
    | .oneMore =>
      if h₁ : i + 1 < bytes.size then
        assemble₂ bytes[i] bytes[i + 1]
      else
        none
    | .twoMore =>
      if h₁ : i + 2 < bytes.size then
        assemble₃ bytes[i] bytes[i + 1] bytes[i + 2]
      else none
    | .threeMore =>
      if h₁ : i + 3 < bytes.size then
        assemble₄ bytes[i] bytes[i + 1] bytes[i + 2] bytes[i + 3]
      else none
  else none

/-! # `utf8DecodeChar?` low-level API -/

theorem parseFirstByte_eq_done_of_utf8DecodeChar?_eq_some {b : ByteArray} {i : Nat} {c : Char}
    (h : utf8DecodeChar? b i = some c) (hc : c.utf8Size = 1) (h') :
    parseFirstByte (b[i]'h') = .done := by
  revert h
  fun_cases utf8DecodeChar? with
  | case1 => simp
  | case2 => simp_all
  | case3 => exact (by omega) ∘ utf8Size_assemble₂
  | case4 => simp
  | case5 => exact (by omega) ∘ utf8Size_assemble₃
  | case6 => simp
  | case7 => exact (by omega) ∘ utf8Size_assemble₄
  | case8 => simp
  | case9 => simp

theorem parseFirstByte_eq_oneMore_of_utf8DecodeChar?_eq_some {b : ByteArray} {i : Nat} {c : Char}
    (h : utf8DecodeChar? b i = some c) (hc : c.utf8Size = 2) (h') :
    parseFirstByte (b[i]'h') = .oneMore := by
  revert h
  fun_cases utf8DecodeChar? with
  | case1 => simp
  | case2 => exact (by omega) ∘ utf8Size_assemble₁
  | case3 => simp_all
  | case4 => simp
  | case5 => exact (by omega) ∘ utf8Size_assemble₃
  | case6 => simp
  | case7 => exact (by omega) ∘ utf8Size_assemble₄
  | case8 => simp
  | case9 => simp

theorem parseFirstByte_eq_twoMore_of_utf8DecodeChar?_eq_some {b : ByteArray} {i : Nat} {c : Char}
    (h : utf8DecodeChar? b i = some c) (hc : c.utf8Size = 3) (h') :
    parseFirstByte (b[i]'h') = .twoMore := by
  revert h
  fun_cases utf8DecodeChar? with
  | case1 => simp
  | case2 => exact (by omega) ∘ utf8Size_assemble₁
  | case3 => exact (by omega) ∘ utf8Size_assemble₂
  | case4 => simp
  | case5 => simp_all
  | case6 => simp
  | case7 => exact (by omega) ∘ utf8Size_assemble₄
  | case8 => simp
  | case9 => simp

theorem parseFirstByte_eq_threeMore_of_utf8DecodeChar?_eq_some {b : ByteArray} {i : Nat} {c : Char}
    (h : utf8DecodeChar? b i = some c) (hc : c.utf8Size = 4) (h') :
    parseFirstByte (b[i]'h') = .threeMore := by
  revert h
  fun_cases utf8DecodeChar? with
  | case1 => simp
  | case2 => exact (by omega) ∘ utf8Size_assemble₁
  | case3 => exact (by omega) ∘ utf8Size_assemble₂
  | case4 => simp
  | case5 => exact (by omega) ∘ utf8Size_assemble₃
  | case6 => simp
  | case7 => simp_all
  | case8 => simp
  | case9 => simp

theorem utf8Size_le_of_utf8DecodeChar?_eq_some {b : ByteArray} {c : Char} :
    utf8DecodeChar? b 0 = some c → c.utf8Size ≤ b.size := by
  fun_cases utf8DecodeChar? with
  | case1 => simp
  | case2 => exact (by omega) ∘ utf8Size_assemble₁
  | case3 => exact (by omega) ∘ utf8Size_assemble₂
  | case4 => simp
  | case5 => exact (by omega) ∘ utf8Size_assemble₃
  | case6 => simp
  | case7 => exact (by omega) ∘ utf8Size_assemble₄
  | case8 => simp
  | case9 => simp

theorem utf8DecodeChar?_eq_assemble₁ {b : ByteArray} (hb : 1 ≤ b.size) (h : parseFirstByte b[0] = .done) :
    utf8DecodeChar? b 0 = assemble₁ b[0] h := by
  fun_cases utf8DecodeChar?
  all_goals try (simp_all; done)
  all_goals omega

theorem utf8DecodeChar?_eq_assemble₂ {b : ByteArray} (hb : 2 ≤ b.size) (h : parseFirstByte b[0] = .oneMore) :
    utf8DecodeChar? b 0 = assemble₂ b[0] b[1] := by
  fun_cases utf8DecodeChar?
  all_goals try (simp_all; done)
  all_goals omega

theorem utf8DecodeChar?_eq_assemble₃ {b : ByteArray} (hb : 3 ≤ b.size) (h : parseFirstByte b[0] = .twoMore) :
    utf8DecodeChar? b 0 = assemble₃ b[0] b[1] b[2] := by
  fun_cases utf8DecodeChar?
  all_goals try (simp_all; done)
  all_goals omega

theorem utf8DecodeChar?_eq_assemble₄ {b : ByteArray} (hb : 4 ≤ b.size) (h : parseFirstByte b[0] = .threeMore) :
    utf8DecodeChar? b 0 = assemble₄ b[0] b[1] b[2] b[3] := by
  fun_cases utf8DecodeChar?
  all_goals try (simp_all; done)
  all_goals omega

theorem utf8DecodeChar?_append_eq_assemble₁ {l : List UInt8} {b : ByteArray} (hl : l.length = 1) (h : parseFirstByte l[0] = .done) :
    utf8DecodeChar? (l.toByteArray ++ b) 0 = assemble₁ l[0] h := by
  have : (l.toByteArray ++ b)[0]'(by simp [hl]; omega) = l[0] := by
    rw [ByteArray.getElem_append_left (by simp [hl]), List.getElem_toByteArray]
  rw [utf8DecodeChar?_eq_assemble₁ (by simp [hl])] <;> simp [this, h]

theorem utf8DecodeChar?_append_eq_assemble₂ {l : List UInt8} {b : ByteArray} (hl : l.length = 2) (h : parseFirstByte l[0] = .oneMore) :
    utf8DecodeChar? (l.toByteArray ++ b) 0 = assemble₂ l[0] l[1] := by
  rw [utf8DecodeChar?_eq_assemble₂ (by simp [hl])]
  all_goals repeat rw [ByteArray.getElem_append_left (by simp [hl])]
  all_goals repeat rw [List.getElem_toByteArray]
  assumption

theorem utf8DecodeChar?_append_eq_assemble₃ {l : List UInt8} {b : ByteArray} (hl : l.length = 3) (h : parseFirstByte l[0] = .twoMore) :
    utf8DecodeChar? (l.toByteArray ++ b) 0 = assemble₃ l[0] l[1] l[2] := by
  rw [utf8DecodeChar?_eq_assemble₃ (by simp [hl])]
  all_goals repeat rw [ByteArray.getElem_append_left (by simp [hl])]
  all_goals repeat rw [List.getElem_toByteArray]
  assumption

theorem utf8DecodeChar?_append_eq_assemble₄ {l : List UInt8} {b : ByteArray} (hl : l.length = 4) (h : parseFirstByte l[0] = .threeMore) :
    utf8DecodeChar? (l.toByteArray ++ b) 0 = assemble₄ l[0] l[1] l[2] l[3] := by
  rw [utf8DecodeChar?_eq_assemble₄ (by simp [hl])]
  all_goals repeat rw [ByteArray.getElem_append_left (by simp [hl])]
  all_goals repeat rw [List.getElem_toByteArray]
  assumption

/-!
# Main theorems

`utf8DecodeChar?_utf8EncodeChar_append` and `toByteArray_of_utf8DecodeChar?_eq_some` are the two main results that together
imply that UTF-8 encoding and decoding are inverse.
-/

theorem utf8DecodeChar?_utf8EncodeChar_append {b : ByteArray} {c : Char} :
    utf8DecodeChar? ((String.utf8EncodeChar c).toByteArray ++ b) 0 = some c := by
  match hc : c.utf8Size, c.utf8Size_pos, c.utf8Size_le_four with
  | 1, _, _ =>
    have hc' : (String.utf8EncodeChar c).length = 1 := String.length_utf8EncodeChar _ ▸ hc
    rw [utf8DecodeChar?_append_eq_assemble₁ hc' (parseFirstByte_utf8EncodeChar_eq_done hc)]
    exact (assemble₁_eq_some_iff_utf8EncodeChar_eq.2 (List.eq_getElem_of_length_eq_one _ hc')).2
  | 2, _, _ =>
    have hc' : (String.utf8EncodeChar c).length = 2 := String.length_utf8EncodeChar _ ▸ hc
    rw [utf8DecodeChar?_append_eq_assemble₂ hc' (parseFirstByte_utf8EncodeChar_eq_oneMore hc)]
    exact (assemble₂_eq_some_iff_utf8EncodeChar_eq.2 (List.eq_getElem_of_length_eq_two _ hc')).2
  | 3, _, _ =>
    have hc' : (String.utf8EncodeChar c).length = 3 := String.length_utf8EncodeChar _ ▸ hc
    rw [utf8DecodeChar?_append_eq_assemble₃ hc' (parseFirstByte_utf8EncodeChar_eq_twoMore hc)]
    exact (assemble₃_eq_some_iff_utf8EncodeChar_eq.2 (List.eq_getElem_of_length_eq_three _ hc')).2
  | 4, _, _ =>
    have hc' : (String.utf8EncodeChar c).length = 4 := String.length_utf8EncodeChar _ ▸ hc
    rw [utf8DecodeChar?_append_eq_assemble₄ hc' (parseFirstByte_utf8EncodeChar_eq_threeMore hc)]
    exact (assemble₄_eq_some_iff_utf8EncodeChar_eq.2 (List.eq_getElem_of_length_eq_four _ hc')).2

theorem toByteArray_of_utf8DecodeChar?_eq_some {b : ByteArray} {c : Char} (h : utf8DecodeChar? b 0 = some c) :
    (String.utf8EncodeChar c).toByteArray = b.extract 0 c.utf8Size := by
  have := utf8Size_le_of_utf8DecodeChar?_eq_some h
  match hc : c.utf8Size, c.utf8Size_pos, c.utf8Size_le_four with
  | 1, _, _ =>
    have := parseFirstByte_eq_done_of_utf8DecodeChar?_eq_some h hc (by omega)
    rw [utf8DecodeChar?_eq_assemble₁ (by omega) this] at h
    rw [ByteArray.extract_add_one (by omega)]
    congr
    rw [← assemble₁_eq_some_iff_utf8EncodeChar_eq]
    exact ⟨this, h⟩
  | 2, _, _ =>
    have := parseFirstByte_eq_oneMore_of_utf8DecodeChar?_eq_some h hc (by omega)
    rw [utf8DecodeChar?_eq_assemble₂ (by omega) this] at h
    rw [ByteArray.extract_add_two (by omega)]
    congr
    rw [← assemble₂_eq_some_iff_utf8EncodeChar_eq]
    exact ⟨this, h⟩
  | 3, _, _ =>
    have := parseFirstByte_eq_twoMore_of_utf8DecodeChar?_eq_some h hc (by omega)
    rw [utf8DecodeChar?_eq_assemble₃ (by omega) this] at h
    rw [ByteArray.extract_add_three (by omega)]
    congr
    rw [← assemble₃_eq_some_iff_utf8EncodeChar_eq]
    exact ⟨this, h⟩
  | 4, _, _ =>
    have := parseFirstByte_eq_threeMore_of_utf8DecodeChar?_eq_some h hc (by omega)
    rw [utf8DecodeChar?_eq_assemble₄ (by omega) this] at h
    rw [ByteArray.extract_add_four (by omega)]
    congr
    rw [← assemble₄_eq_some_iff_utf8EncodeChar_eq]
    exact ⟨this, h⟩

/-! # Corollaries -/

theorem eq_of_utf8DecodeChar?_eq_some {b : ByteArray} {c : Char} (h : utf8DecodeChar? b 0 = some c) :
    b = (String.utf8EncodeChar c).toByteArray ++ b.extract c.utf8Size b.size := by
  rw [toByteArray_of_utf8DecodeChar?_eq_some h,
    ByteArray.extract_append_extract, Nat.zero_min, Nat.max_eq_right (utf8Size_le_of_utf8DecodeChar?_eq_some h),
    ByteArray.extract_zero_size]

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

theorem lt_size_of_isSome_utf8DecodeChar? {b : ByteArray} {i : Nat} (h : (utf8DecodeChar? b i).isSome) :
    i < b.size := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 h
  have := le_size_of_utf8DecodeChar?_eq_some hc
  have := c.utf8Size_pos
  omega

theorem utf8DecodeChar?_append_eq_some {b : ByteArray} {i : Nat} {c : Char} (h : utf8DecodeChar? b i = some c)
    (b' : ByteArray) : utf8DecodeChar? (b ++ b') i = some c := by
  have := le_size_of_utf8DecodeChar?_eq_some h
  rw [utf8DecodeChar?_eq_utf8DecodeChar?_drop] at ⊢ h
  rw [ByteArray.extract_eq_extract_append_extract b.size (by omega) (by simp), ByteArray.extract_append_size_left,
    eq_of_utf8DecodeChar?_eq_some h, ByteArray.append_assoc, utf8DecodeChar?_utf8EncodeChar_append]

theorem isSome_utf8DecodeChar?_append {b : ByteArray} {i : Nat} (h : (utf8DecodeChar? b i).isSome)
    (b' : ByteArray) : (utf8DecodeChar? (b ++ b') i).isSome := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 h
  rw [utf8DecodeChar?_append_eq_some hc, Option.isSome_some]

def utf8DecodeChar (bytes : ByteArray) (i : Nat) (h : (utf8DecodeChar? bytes i).isSome) : Char :=
  (utf8DecodeChar? bytes i).get h

end decode
