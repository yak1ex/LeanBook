import LeanBook.IntMathlib.Mul

/- 8.5 整数は前順序 -/

/- 8.5.1 自然数を整数の部分集合だとみなす -/

/-- 定数関数を返す -/
private def MyInt.const (x : MyInt) : MyInt → MyInt := fun _ => x

#check_failure MyInt.const (0 : MyNat) -- Application type mismatch

/-- 自然数から整数への変換 -/
def MyInt.ofMyNat (n : MyNat) : MyInt := ⟦(n, 0)⟧

-- エラーが消える
#check MyInt.const (.ofMyNat 0)

/- 型強制で自動的に変換する -/
instance : Coe MyNat MyInt where
  coe := MyInt.ofMyNat

#check MyInt.const (0 : MyNat) -- MyInt.const (MyInt.ofMyNat 0) : MyInt → MyInt

/- 内部実装を隠蔽する -/
example : ((0 : MyNat) : MyInt) = (0 : MyInt) := by
  -- 内部実装である MyInt.ofMyNat が見えてしまう(本来は見えないようにしたい)
  guard_target =ₛ MyInt.ofMyNat 0 = 0
  sorry

-- MyInt.ofMyNat を型キャストとして認識させる
attribute [coe] MyInt.ofMyNat

@[simp]
theorem MyInt.ofMyNat_zero_eq_zero : MyInt.ofMyNat 0 = (0 : MyInt) := by
  dsimp [MyInt.ofMyNat]
  rfl

example : ((0 : MyNat) : MyInt) = (0 : MyInt) := by
  -- 内部実装である MyInt.ofMyNat が見えなくなった
  guard_target =ₛ ↑ (0 : MyNat) = (0 : MyInt)
  rfl

/- norm_cast : 型キャストを外す -/
@[norm_cast]
theorem MyInt.ofMyNat_inj {m n : MyNat}
    : (m : MyInt) = (n : MyInt) ↔ m = n := by
  -- 双方向を示すことで証明する
  constructor <;> intro h
  -- ↑m = ↑n → m = n を示す
  case mp =>
    -- このとき (m, 0) と (n, 0) は PreInt として同値である
    have : (m, 0) ≈ (n, 0) := by
      exact Quotient.exact h
    -- これはつまり　m + 0 = 0 + n と言い換えられる
    notation_simp at this
    -- ここから結論が従う
    simp_all
  -- m = n → ↑m = ↑n は明らか
  case mpr => rw [h]

@[simp]
theorem MyInt.ofMyNat_eq_zero {n : MyNat} : (n : MyInt) = 0 ↔ n = 0 := by
  constructor <;> intro h
  · rw [show (0 : MyInt) = ↑ (0 : MyNat) from rfl] at h
    norm_cast at h
  · simp_all

/- push_cast : 型キャストを内側へ移動させる -/
@[push_cast]
theorem MyInt.ofMyNat_add (m n : MyNat)
  : ↑ (m + n) = (m : MyInt) + (n : MyInt) := by
  rfl

/- 8.5.2 順序の定義 -/

/-- 整数の広義順序 -/
def MyInt.le (m n : MyInt) : Prop :=
  ∃ k : MyNat, m + ↑ k = n

instance : LE MyInt where
  le := MyInt.le

@[notation_simp]
theorem MyInt.le_def (m n : MyInt) : m ≤ n ↔ ∃ k : MyNat, m + ↑ k = n := by
  rfl

/- 8.5.3 前順序であることを確かめて再利用可能にする -/

/- 反射律 -/
@[refl]
theorem MyInt.le_refl (m : MyInt) : m ≤ m := by
  exists 0
  simp

/- 推移律 -/
theorem MyInt.le_trans {m n k : MyInt} (hnm : n ≤ m) (hmk : m ≤ k) : n ≤ k := by
  -- ≤ は和の等式で定義されていたことを思い出す
  -- したがって n + ↑l = k を満たす l を構成すればよい
  notation_simp at *
  -- 仮定からある a と b が存在して
  -- n + ↑ a = m と m + ↑ b = k が成り立つ
  obtain ⟨a, ha⟩ := hnm
  obtain ⟨b, hb⟩ := hmk
  -- このとき a + b が求める条件を満たす
  use a + b
  -- これを正当化するには n + ↑ (a + b) = k を示せばよいが、
  -- これは n + ↑ a + ↑ b = k と同じことであり
  push_cast
  -- 仮定から計算すれば示せる
  have : n + (↑ a + ↑ b) = k := by calc
    _ = (n + ↑ a) + ↑ b := by ac_rfl
    _ = m + ↑ b := by rw[ha]
    _ = k := by rw[hb]
  assumption

/- 前順序であることを再利用可能にする -/
instance : Preorder MyInt where
  le_refl := MyInt.le_refl
  le_trans := by
    intros a b c hab hbc
    apply MyInt.le_trans hab hbc

example (a b c : MyInt) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  order

/- 8.5.4 練習問題 -/
example (a b : MyInt) (h1 : a ≤ b) (h2 : ¬ (a < b)) : b ≤ a := by
  order
