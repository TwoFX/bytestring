@[simp]
theorem ByteArray.data_empty : ByteArray.empty.data = #[] := rfl

@[simp]
theorem ByteArray.data_extract {a : ByteArray} {b e : Nat} :
    (a.extract b e).data = a.data.extract b e := by
  simp [extract, copySlice]
  grind

@[simp]
theorem ByteArray.size_data {a : ByteArray} :
  a.data.size = a.size := rfl

@[simp]
theorem ByteArray.extract_zero_size {b : ByteArray} : b.extract 0 b.size = b := by
  ext1
  simp

@[simp]
theorem ByteArray.extract_same {b : ByteArray} {i : Nat} : b.extract i i = ByteArray.empty := by
  ext1
  simp [Nat.min_le_left]
