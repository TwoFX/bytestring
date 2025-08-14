attribute [ext] ByteArray

theorem ByteArray.append_eq_copySlice {a b : ByteArray} :
  a ++ b = b.copySlice 0 a a.size b.size false := rfl

@[simp]
theorem ByteArray.size_data {a : ByteArray} :
  a.data.size = a.size := rfl

@[simp]
theorem ByteArray.data_append {l l' : ByteArray} :
    (l ++ l').data = l.data ++ l'.data := by
  simp [append_eq_copySlice, copySlice, ← ByteArray.size_data, - Array.append_assoc]

@[simp]
theorem ByteArray.data_push {a : ByteArray} {b : UInt8} :
    (a.push b).data = a.data.push b := rfl

@[simp]
theorem ByteArray.data_empty : ByteArray.empty.data = #[] := rfl

@[simp]
theorem ByteArray.size_empty : ByteArray.empty.size = 0 := by
  simp [← ByteArray.size_data]

@[simp]
theorem List.data_toByteArray {l : List UInt8} :
    l.toByteArray.data = l.toArray := by
  rw [List.toByteArray]
  suffices ∀ a b, (List.toByteArray.loop a b).data = b.data ++ a.toArray by
    simpa using this l ByteArray.empty
  intro a b
  fun_induction List.toByteArray.loop a b with simp_all

@[simp]
theorem List.size_toByteArray {l : List UInt8} :
    l.toByteArray.size = l.length := by
  simp [← ByteArray.size_data]

@[simp]
theorem List.toByteArray_append {l l' : List UInt8} :
    (l ++ l').toByteArray = l.toByteArray ++ l'.toByteArray := by
  ext1
  simp

@[simp]
theorem List.toByteArray_nil : List.toByteArray [] = ByteArray.empty := rfl

@[simp]
theorem ByteArray.empty_append {b : ByteArray} : ByteArray.empty ++ b = b := by
  ext1
  simp

@[simp]
theorem ByteArray.append_empty {b : ByteArray} : b ++ ByteArray.empty = b := by
  ext1
  simp

@[simp, grind]
theorem ByteArray.size_append {a b : ByteArray} : (a ++ b).size = a.size + b.size := by
  simp [← size_data]

@[simp]
theorem ByteArray.size_eq_zero_iff {a : ByteArray} : a.size = 0 ↔ a = ByteArray.empty := by
  refine ⟨fun h => ?_, fun h => h ▸ ByteArray.size_empty⟩
  ext1
  simp [← Array.size_eq_zero_iff, h]

theorem ByteArray.getElem_eq_getElem_data {a : ByteArray} {i : Nat} {h : i < a.size} :
    a[i] = a.data[i]'(by simpa [← size_data]) := rfl

@[simp]
theorem ByteArray.getElem_append_left {i : Nat} {a b : ByteArray} {h : i < (a ++ b).size}
    (hlt : i < a.size) : (a ++ b)[i] = a[i] := by
  simp only [getElem_eq_getElem_data, data_append]
  rw [Array.getElem_append_left (by simpa)]

theorem ByteArray.getElem_append_right {i : Nat} {a b : ByteArray} {h : i < (a ++ b).size}
    (hle : a.size ≤ i) : (a ++ b)[i] = b[i - a.size]'(by simp_all; omega) := by
  simp only [getElem_eq_getElem_data, data_append]
  rw [Array.getElem_append_right (by simpa)]
  simp

@[simp]
theorem List.getElem_toByteArray {l : List UInt8} {i : Nat} {h : i < l.toByteArray.size} :
    l.toByteArray[i] = l[i]'(by simp_all) := by
  simp [ByteArray.getElem_eq_getElem_data]

def ByteArray.drop (b : ByteArray) (i : Nat) : ByteArray :=
  b.extract i b.size

@[simp]
theorem ByteArray.drop_eq_extract {b : ByteArray} {i : Nat} :
  b.drop i = b.extract i b.size := rfl

@[simp]
theorem ByteArray.data_extract {a : ByteArray} {b e : Nat} :
    (a.extract b e).data = a.data.extract b e := by
  simp [extract, copySlice]
  grind

@[simp]
theorem ByteArray.size_extract {a : ByteArray} {b e : Nat} :
    (a.extract b e).size = min e a.size - b := by
  simp [← size_data]

@[simp]
theorem ByteArray.extract_size_size {b : ByteArray} : b.extract b.size b.size = ByteArray.empty := by
  ext1
  simp

@[simp]
theorem ByteArray.extract_eq_empty_iff {b : ByteArray} {i j : Nat} : b.extract i j = ByteArray.empty ↔ min j b.size ≤ i := by
  rw [← size_eq_zero_iff, size_extract]
  omega

@[simp]
theorem ByteArray.extract_zero_size {b : ByteArray} : b.extract 0 b.size = b := by
  ext1
  simp

@[simp]
theorem ByteArray.append_eq_empty_iff {a b : ByteArray} :
    a ++ b = ByteArray.empty ↔ a = ByteArray.empty ∧ b = ByteArray.empty := by
  simp [← size_eq_zero_iff, size_append]

@[simp]
theorem List.toByteArray_eq_empty {l : List UInt8} :
    l.toByteArray = ByteArray.empty ↔ l = [] := by
  simp [← ByteArray.size_eq_zero_iff]

theorem ByteArray.append_right_inj {ys₁ ys₂ : ByteArray} (xs : ByteArray) :
    xs ++ ys₁ = xs ++ ys₂ ↔ ys₁ = ys₂ := by
  simp [ByteArray.ext_iff, Array.append_right_inj]

@[simp]
theorem ByteArray.extract_append_extract {a : ByteArray} {i j k : Nat} :
    a.extract i j ++ a.extract j k = a.extract (min i j) (max j k) := by
  ext1
  simp

theorem ByteArray.extract_eq_extract_append_extract {a : ByteArray} {i k : Nat} (j : Nat)
    (hi : i ≤ j) (hk : j ≤ k) :
    a.extract i k = a.extract i j ++ a.extract j k := by
  simp; grind

--  {α : Type u_1} {xs₁ xs₂ ys₁ ys₂ : Array α} (h : xs₁ ++ ys₁ = xs₂ ++ ys₂) (hl : xs₁.size = xs₂.size) : xs₁ = xs₂

theorem ByteArray.append_inj_left {xs₁ xs₂ ys₁ ys₂ : ByteArray} (h : xs₁ ++ ys₁ = xs₂ ++ ys₂) (hl : xs₁.size = xs₂.size) : xs₁ = xs₂ := by
  simp only [ByteArray.ext_iff, ← ByteArray.size_data, ByteArray.data_append] at *
  exact Array.append_inj_left h hl

theorem ByteArray.extract_append_eq_right {a b : ByteArray} {i : Nat} (hi : i = a.size) :
    (a ++ b).extract i (a ++ b).size = b := by
  subst hi
  ext1
  simp [← size_data]
