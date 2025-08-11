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
theorem List.data_toByteArray {l : List UInt8} :
    l.toByteArray.data = l.toArray := by
  rw [List.toByteArray]
  suffices ∀ a b, (List.toByteArray.loop a b).data = b.data ++ a.toArray by
    simpa using this l ByteArray.empty
  intro a b
  fun_induction List.toByteArray.loop a b with simp_all

@[simp]
theorem List.toByteArray_append {l l' : List UInt8} :
    (l ++ l').toByteArray = l.toByteArray ++ l'.toByteArray := by
  ext1
  simp
