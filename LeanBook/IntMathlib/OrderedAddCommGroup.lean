import LeanBook.IntMathlib.PartialOrder

/- 8.7 整数は足し算に関して可換な順序群 -/

/- 8.7.1 MyInt を順序軍にする -/

theorem MyInt.add_le_add_left (a b : MyInt) (h : a ≤ b) (c : MyInt)
  : c + a ≤ c + b := by
  -- ≤ の定義により a + ↑ m = b を満たす m : MyNat が存在する
  -- このとき ∃ k, c + a + ↑ k = c + b を示せばよい
  notation_simp at h
  obtain ⟨m, hm⟩ := h
  -- ここで k = m とすればよい
  use m
  -- 正当化は結合法則と m の定義から従う
  have : c + a + ↑ m = c + b := by calc
    _ = c + (a + ↑ m) := by ac_rfl
    _ = c + b := by rw[hm]
  assumption

instance : IsOrderedAddMonoid MyInt where
  add_le_add_left := MyInt.add_le_add_left

/- 8.7.2 練習問題 -/

/-- 非負の整数は自然数に対応する -/
example (a : MyInt) (nneg : 0 ≤ a) : ∃ k : MyNat, a = ↑ k := by
  -- ≤ の定義により 0 + ↑ m = a を満たす m : MyNat が存在する
  notation_simp at nneg
  obtain ⟨k, hk⟩ := nneg
  -- したがって a = ↑ m が成り立つ
  exists k
  simp_all
