import LeanBook.IntMathlib.DecidableOrd

/- 8.9 整数は全順序 -/

/- 8.9.1 a ≤ b ∨ b ≤ a -/
/-- すべての整数 a に対して 0 ≤ a または 0 ≤ -a のいずれかが成り立つ -/
theorem MyInt.nonneg_or_nonneg_neg {a : MyInt} : 0 ≤ a ∨ 0 ≤ -a := by
  -- a : MyInt の代表元を取る
  induction a using Quotient.inductionOn with
  | h a =>
    -- a = ⟦(m, n)⟧ と表せるとする
    obtain ⟨m, n⟩ := a
    -- このとき自然数については全順序であることがすでに示せているので
    -- m ≤ n または n ≤ m のいずれかが成り立つ
    have : n ≤ m ∨ m ≤ n := by
      exact MyNat.le_total n m
    -- どちらが成り立つかについて場合分けをすれば示せる
    cases this with
    | inl h =>
      left
      simp [mk_def]
      norm_cast
    | inr h =>
      right
      simp [mk_def]
      norm_cast

/-- 整数は全順序 -/
theorem MyInt.le_total (a b : MyInt) : a ≤ b ∨ b ≤ a := by
  suffices goal : 0 ≤ b - a ∨ 0 ≤ - (b - a) from by
    cases goal with
    | inl h =>
      left
      rw [← MyInt.sub_nonneg]
      assumption
    | inr h =>
      right
      rw [← MyInt.sub_nonneg]
      rw [show -(b - a) = a - b from by abel] at h
      assumption
  exact nonneg_or_nonneg_neg

instance : LinearOrder MyInt where
  toDecidableLE := by infer_instance
  le_total := by exact MyInt.le_total

/- 8.9.2 n ≤ m ↔ n = m ∨ n < m -/

theorem MyInt.eq_or_lt_of_le (a b : MyInt) (h : a ≤ b) : a = b ∨ a < b := by
  by_cases hor : a = b
  case pos =>
    left
    assumption
  case neg =>
    right
    order

theorem MyInt.le_of_eq_or_lt {a b : MyInt} (h : a = b ∨ a < b) : a ≤ b := by
  cases h with
  | inl h => rw [h]
  | inr _ => order

/-- 広義順序 ≤ は等号 = と狭義順序 < で書き換えられる -/
theorem MyInt.le_iff_eq_or_lt {m n : MyInt} : m ≤ n ↔ m = n ∨ m < n := by
  constructor
  case mp => apply MyInt.eq_or_lt_of_le
  case mpr => apply MyInt.le_of_eq_or_lt

/- 8.9.3 練習問題 -/
example {a b : MyInt} (h : b < a) : ¬ (a ≤ b) := by
  order

/-- 0 以下の数はマイナスを取ると 0 以上になる -/
example {a : MyInt} (neg : a ≤ 0) : - a ≥ 0 := by
  have : 0 ≤ a ∨ 0 ≤ - a := by
    exact MyInt.nonneg_or_nonneg_neg
  cases this with
  | inl h =>
    have : a = 0 := by order
    rw [this]
    simp
  | inr h => exact h
