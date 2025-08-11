attribute [ext] ByteArray

theorem ByteArray.append_eq_copySlice {a b : ByteArray} :
  a ++ b = b.copySlice 0 a a.size b.size false := rfl

@[simp]
theorem ByteArray.size_data {a : ByteArray} :
  a.data.size = a.size := rfl

@[simp]
theorem ByteArray.data_append {l l' : ByteArray} :
    (l ++ l').data = l.data ++ l'.data := by
  simp [append_eq_copySlice, copySlice, ← ByteArray.size_data, ← Array.append_assoc]

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
theorem List.toByteArray_empty : List.toByteArray [] = ByteArray.empty := rfl

@[simp]
theorem ByteArray.empty_append {b : ByteArray} : ByteArray.empty ++ b = b := by
  ext1
  simp

@[simp]
theorem ByteArray.size_append {a b : ByteArray} : (a ++ b).size = a.size + b.size := by
  simp [← size_data]

@[simp]
theorem ByteArray.size_eq_zero_iff {a : ByteArray} : a.size = 0 ↔ a = ByteArray.empty := by
  refine ⟨fun h => ?_, fun h => h ▸ ByteArray.size_empty⟩
  ext1
  simp [← Array.size_eq_zero_iff, h]

theorem ByteArray.getElem_eq_getElem_data {a : ByteArray} {i : Nat} {h : i < a.size} :
    a[i] = a.data[i]'(by simpa [← size_data]) := rfl

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
