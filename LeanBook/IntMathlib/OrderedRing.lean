import LeanBook.IntMathlib.LinearOrder

/- 8.10 整数は順序環 -/

/- 8.10.1 IsStrictOrderedRing -/

/- 狭義順序を足し算の等式に書き換える -/

variable {a b c : MyInt}

/-- 狭義順序 < を足し算の等式に変形する -/
theorem MyInt.lt.dest (h : a < b) : ∃ k : MyNat, a + (↑ k + 1) = b := by
  -- < の定義により a ≤ b ∧ ¬ (b ≤ a) が成り立つ
  -- ここで a ≤ b の定義より a + ↑ k = b となる自然数 k : MyNat が存在する
  -- 一方で b + ↑ n = a となる自然数 n : MyNat は存在しない
  notation_simp at h
  obtain ⟨⟨k, hk⟩, h⟩ := h

  -- k についての場合分けで示す
  induction k with
  | zero =>
    -- k = 0 のときは矛盾を示せば良い
    exfalso
    -- このとき a + 0 = b となるので b = a が成り立つ
    replace hk : a = b := by simp_all
    -- これは b + ↑ n = a となる自然数 n : MyNat は存在しないという仮定に矛盾する
    have : ∃ k : MyNat, b + ↑ k = a := by
      rw [hk]
      exists 0
      simp
    contradiction
  | succ k _ =>
    -- k + 1 のケースは明らか
    push_cast at hk
    use k
    assumption

theorem MyInt.le.intro (a : MyInt) (b : MyNat) : a ≤ a + ↑ b := by
  use b

theorem MyInt.lt.intro (h : ∃ k : MyNat, a + (k + 1) = b) : a < b := by
  obtain ⟨k, hk⟩ := h
  -- a < b の定義により a ≤ b ∧ ¬ (b ≤ a) を示せばよい
  simp only [lt_def]
  -- 1つずつ示していく
  constructor

  case left =>
    -- a ≤ b の定義から ∃ k, a + ↑ k = b を示せばよい
    notation_simp
    -- これは仮定から明らか
    use k + 1
    assumption

  case right =>
    -- b ≤ a の定義から ¬ ∃ k, b + ↑ k = a を示せばよい
    notation_simp
    -- b + ↑s = a となる自然数 s : MyNat が存在したと仮定する
    intro ⟨s, hs⟩

    -- このとき整数は足し算について可換群なので特にキャンセル可能であり
    -- 仮定から ↑ (s + k) + (1 : MyInt) = 0 が成り立つ
    rw [← hs] at hk
    have : ↑ (s + k) + (1 : MyInt) = 0 := by calc
      _ = (↑ s + ↑ k) + (1 : MyInt) := by push_cast; rfl
      _ = (b + ↑ s + (↑ k + 1)) - b := by abel
      _ = b - b := by rw[hk]
      _ = 0 := by abel

    -- これは 0 > 0 を意味し矛盾である
    replace : (0 : MyInt) > 0 := calc
      _ = ↑ (s + k) + (1 : MyInt) := by rw [this]
      _ = (1: MyInt) + ↑ (s + k) := by ac_rfl
      _ ≥ (1: MyInt) := by apply MyInt.le.intro
      _ > (0 : MyInt) := by decide
    order

/-- 狭義の順序関係 < を足し算で書き換える -/
theorem MyInt.lt_iff_add : a < b ↔ ∃ k : MyNat, a + (k + 1) = b := by
  constructor
  case mp => apply MyInt.lt.dest
  case mpr => apply MyInt.lt.intro

/- 掛け算が正数を保つことの証明 -/

@[push_cast]
theorem MyInt.ofMyNat_mul (m n : MyNat)
  : ↑ (m * n) = (m : MyInt) * (n : MyInt) := by
  dsimp [MyInt.ofMyNat]
  apply Quotient.sound
  notation_simp
  ring

/-- 正の整数の掛け算は再び正 -/
theorem MyInt.mul_pos (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  rw [MyInt.lt_iff_add] at *
  obtain ⟨c, hc⟩ := ha
  obtain ⟨d, hd⟩ := hb
  rw [← hc, ← hd]
  use c * d + c + d
  push_cast
  ring

/- 掛け算が狭義順序を保つことを示す -/

theorem MyInt.sub_pos : 0 < a - b ↔ b < a := by
  constructor <;> intro h
  · rw [MyInt.lt_iff_add] at *
    obtain ⟨k, hk⟩ := h
    simp at hk
    use k
    rw [hk]
    abel
  · rw [MyInt.lt_iff_add] at *
    obtain ⟨k, hk⟩ := h
    use k
    rw [← hk]
    abel

theorem MyInt.mul_lt_mul_of_pos_left (h : a < b) (pos : 0 < c)
  : c * a < c * b := by
  suffices 0 < c * (b - a) from by
    rw [MyInt.lt_iff_add] at this ⊢
    obtain ⟨k, hk⟩ := this
    simp at hk
    use k
    rw [hk]
    simp [MyInt.left_distrib]
  replace h : 0 < b - a := by
    rw [MyInt.sub_pos]
    assumption
  apply MyInt.mul_pos (ha := pos) (hb := h)

theorem MyInt.mul_lt_mul_of_pos_right (h : a < b) (pos : 0 < c)
  : a * c < b * c := by
  rw [MyInt.mul_comm a c, MyInt.mul_comm b c]
  apply MyInt.mul_lt_mul_of_pos_left (h := h) (pos := pos)

instance : IsStrictOrderedRing MyInt where
  zero_le_one := by decide
  exists_pair_ne := by exists 0, 1
  mul_lt_mul_of_pos_left := by apply MyInt.mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right := by apply MyInt.mul_lt_mul_of_pos_right

example (a b c : MyInt) (h : a < b) : a + c < b + c := by
  linarith

example (a b : MyInt) (h1 : 2 * a - b = 1) (h2 : a + b = 5) : a = 2 := by
  -- 連立方程式も解いてくれる
  linarith

/- 8.10.2 IsOrderedRing を示す -/

/-- 左からの掛け算は広義順序を保つ -/
theorem MyInt.mul_le_mul_of_nonneg_left (h : a ≤ b) (nneg : 0 ≤ c)
  : c * a ≤ c * b := by
  nlinarith

/-- 右からの掛け算は広義順序を保つ -/
theorem MyInt.mul_le_mul_of_nonneg_right (h : a ≤ b) (nneg : 0 ≤ c)
  : a * c ≤ b * c := by
  nlinarith

instance : IsOrderedRing MyInt where
  zero_le_one := by decide
  mul_le_mul_of_nonneg_left := by apply MyInt.mul_le_mul_of_nonneg_left
  mul_le_mul_of_nonneg_right := by apply MyInt.mul_le_mul_of_nonneg_right

/- 8.10.3 練習問題 -/

example (a b : MyInt) (h1 : 3 * a - 2 * b = 5) (h2 : 6 * a -5 *b = 11)
  : b = -1 := by
  linarith
