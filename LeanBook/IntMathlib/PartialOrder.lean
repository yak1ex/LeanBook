import LeanBook.IntMathlib.PreOrder

/- 8.6 整数は半順序 -/

/- 8.6.1 証明 -/

@[simp↓]
theorem MyInt.add_right_eq_self (a b : MyInt) : a + b = a ↔ b = 0 := by
  -- 双方向を示す
  constructor <;> intro h
  -- 左から右は
  case mp => calc
    -- 整数がアーベル群であることと仮定から、計算すれば示せる
    _ = b := by rfl
    _ = a + b - a := by abel
    _ = a - a := by rw [h]
    _ = 0 := by abel
  -- 右から左は明らか
  case mpr =>
    simp [h]

theorem MyInt.le_antisymm (a b : MyInt) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  -- ≤ の定義により a + ↑ m = b かつ b + ↑ n = a を満たす m, n : MyNat が存在する
  notation_simp at *
  obtain ⟨m, hm⟩ := h1
  obtain ⟨n, hn⟩ := h2
  -- このとき自然数は結合法則が成り立つので
  have : a + (↑ m + ↑ n) = a := by calc
    _ = a + ↑ m + ↑ n := by ac_rfl
    _ = b + ↑ n := by rw[hm]
    _ = a := by rw[hn]
  -- これは、補題より ↑ (m + n) = 0 を意味する
  replace : ↑ (m + n) = (0 : MyInt) := by
    push_cast
    simp_all
  -- よって m + n = 0 が成り立つ
  have ⟨mz, nz⟩ : m = 0 ∧ n = 0 := by
    simp_all
  -- これで題意は示された
  simp_all

instance : PartialOrder MyInt where
  le_antisymm := MyInt.le_antisymm

-- order で利用可能になった
example (a b : MyInt) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  order

/- 8.6.2 練習問題 -/
example (a b : MyInt) (h : a = b ∨ a < b) : a ≤ b := by
  cases h <;> order
