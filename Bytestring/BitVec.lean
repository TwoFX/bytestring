namespace BitVec

def ult' (b b' : BitVec w) : Bool :=
  match w with
  | 0 => false
  | w' + 1 =>
    match b.msb, b'.msb with
    | false, true => true
    | true, false => false
    | false, false => ult' (b.setWidth w') (b'.setWidth w')
    | true, true => ult' (b.setWidth w') (b'.setWidth w')

theorem ult_zero_length {b b' : BitVec 0} : b.ult b' = false := by
  simp [BitVec.ult, BitVec.toNat_zero_length]

theorem toNat_div_two_pow {b : BitVec (w + 1)} : b.toNat / 2 ^ w = if b.msb then 1 else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_div_two_pow]
  cases i with
  | zero =>
    rw [Nat.zero_add, testBit_toNat, BitVec.msb_eq_getLsbD_last,
      Nat.add_sub_cancel]
    split <;> simp_all
  | succ i =>
    rw [testBit_toNat, getLsbD_of_ge _ _ (by omega)]
    split <;> simp [← Bool.not_eq_true, Nat.testBit_one_eq_true_iff_self_eq_zero]

theorem ult'_eq_ult {b b' : BitVec w} : ult' b b' = BitVec.ult b b' := by
  fun_induction ult' with
  | case1 => simp [ult_zero_length]
  | case2 w' b b' h₁ h₂ => simp_all [ult_eq_msb_of_msb_neq]
  | case3 => simp_all [ult_eq_msb_of_msb_neq]
  | case4 w' b b' h₁ h₂ ih  =>
    rw [ih, ult_eq_decide, ult_eq_decide, decide_eq_decide, toNat_setWidth,
      toNat_setWidth]
    conv => rhs; rw [← Nat.div_add_mod b.toNat (2 ^ w'), ← Nat.div_add_mod b'.toNat (2 ^ w')]
    simp [toNat_div_two_pow, h₁, h₂]
  | case5 w' b b' h₁ h₂ ih =>
    rw [ih, ult_eq_decide, ult_eq_decide, decide_eq_decide, toNat_setWidth,
      toNat_setWidth]
    conv => rhs; rw [← Nat.div_add_mod b.toNat (2 ^ w'), ← Nat.div_add_mod b'.toNat (2 ^ w')]
    simp [toNat_div_two_pow, h₁, h₂]

set_option grind.warning false

theorem lt_iff_getElem {b b' : BitVec w} :
    b < b' ↔ ∃ (i : Nat) (h : i < w), b[i] = false ∧ b'[i] = true ∧ ∀ j, i < j → (_ : j < w) → b[j] = b'[j] := by
  rw [← ult_iff_lt, ← ult'_eq_ult]
  fun_induction ult' with
  | case1 => simp
  | case2 w' b b' h₁ h₂ =>
    simp only [Nat.succ_eq_add_one, true_iff]
    refine ⟨w', by omega, ?_, ?_, by omega⟩
    · rw [msb_eq_getLsbD_last, Nat.add_sub_cancel] at h₁
      rwa [← getLsbD_eq_getElem]
    · rw [msb_eq_getLsbD_last, Nat.add_sub_cancel] at h₂
      rwa [← getLsbD_eq_getElem]
  | case3 w' b b' h₁ h₂ =>
    simp only [Bool.false_eq_true, Nat.succ_eq_add_one, false_iff, not_exists, _root_.not_and,
      Classical.not_forall]
    intro j hj hj₁ hj₂
    rw [msb_eq_getLsbD_last, Nat.add_sub_cancel] at h₁ h₂
    rw [← getLsbD_eq_getElem] at hj₁ hj₂
    refine ⟨w', ?_, by omega, ?_⟩
    · exact Or.elim (by omega : j < w' ∨ j = w') id (by rintro rfl; simp_all)
    · simp [← getLsbD_eq_getElem, h₁, h₂]
  | case4 w' b b' h₁ h₂ ih =>
    rw [msb_eq_getLsbD_last, Nat.add_sub_cancel] at h₁ h₂
    simp only [ih, ← getLsbD_eq_getElem, getLsbD_setWidth, Bool.and_eq_false_imp, decide_eq_true_eq,
      Bool.and_eq_true, exists_and_left, exists_prop, Nat.succ_eq_add_one]
    refine ⟨fun ⟨i, hi⟩ => ⟨i, by grind, by grind, by grind, ?_⟩,
      fun ⟨i, hi⟩ => ⟨i, by grind, by grind, by grind, ?_⟩⟩
    · exact fun j hj hjw' => Or.elim (by omega : j = w' ∨ j < w') (by grind) (by grind)
    · refine fun j hj hjw' => ?_
      simp only [hjw', decide_true, Bool.true_and]
      exact hi.2.2.2 _ hj (by omega)
  | case5 w' b b' h₁ h₂ ih =>
    rw [msb_eq_getLsbD_last, Nat.add_sub_cancel] at h₁ h₂
    simp only [ih, ← getLsbD_eq_getElem, getLsbD_setWidth, Bool.and_eq_false_imp, decide_eq_true_eq,
      Bool.and_eq_true, exists_and_left, exists_prop, Nat.succ_eq_add_one]
    refine ⟨fun ⟨i, hi⟩ => ⟨i, by grind, by grind, by grind, ?_⟩,
      fun ⟨i, hi⟩ => ⟨i, by grind, by grind, by grind, ?_⟩⟩
    · exact fun j hj hjw' => Or.elim (by omega : j = w' ∨ j < w') (by grind) (by grind)
    · refine fun j hj hjw' => ?_
      simp only [hjw', decide_true, Bool.true_and]
      exact hi.2.2.2 _ hj (by omega)

end BitVec
