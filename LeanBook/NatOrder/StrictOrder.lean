import LeanBook.NatOrder.OrderDef

/- 6.3 狭義順序を定義する -/

/- 6.3.1 狭義順序の定義 -/
/-- m < n を表す -/
def MyNat.lt (m n : MyNat) : Prop := m + 1 ≤ n

/-- a < b という書き方ができるようにする -/
instance : LT MyNat where
  lt := MyNat.lt

example (m n : MyNat) : m < n ↔ m + 1 ≤ n := by
  /- dsimp [(· < ·), MyNat.lt] -/ -- なしでも通る
  rfl

/- 6.3.2 狭義順序と広義順序、統合の関係 -/

/- 補題1 -/
/-- 1 ≠ 0 が成り立つ -/
@[simp] theorem MyNat.one_neq_zero : 1 ≠ 0 := by
  intro h
  injection h

/-- 0 ≠ 1 が成り立つ -/
@[simp] theorem MyNat.zero_neq_one : 0 ≠ 1 := by
  intro h
  injection h

/- 補題2 -/
/-- 任意の自然数は 0 以上である -/
@[simp] theorem MyNat.zero_le (n : MyNat) : 0 ≤ n := by
  -- ≤ を和の等式に帰着させると
  rw [MyNat.le_iff_add]
  -- 示すべきことは ∃ k, 0 + k = n であるが、これは k = n とすれば成り立つ
  exists n
  simp

/-- 0 以下の自然数は 0 しかない -/
theorem MyNat.zeo_of_le_zero {n : MyNat} (h : n ≤ 0) : n = 0 := by
  -- n についての帰納法で示す
  induction n with
  | zero =>
    -- n = 0 のときは明らか
    simp
  | succ n ih =>
    -- n + 1 ≤ 0 という仮定が得られるが、これはありえない
    -- そこで矛盾を示す
    exfalso
    -- ≤ を和の等式に書き換えると
    -- ある k が存在して n + 1 + k = 0 を満たすことがわかる
    rw [MyNat.le_iff_add] at h
    obtain ⟨k, hk⟩ := h
    -- しかし n + 1 + k が 0 になることはあり得ないありえないので矛盾
    simp_all

/-- 0 以下の自然数は 0 しかない -/
@[simp] theorem MyNat.le_zero (n : MyNat) : n ≤ 0 ↔ n = 0 := by
  constructor <;> intro h
  · apply MyNat.zeo_of_le_zero h
  · simp [h]

/-- 任意の自然数は 0 か正 -/
theorem MyNat.eq_zero_or_pos (n : MyNat) : n = 0 ∨ 0 < n := by
  -- n についての帰納法で示す
  induction n with
  | zero =>
    -- n = 0 のときは明らか
    simp
  | succ n ih =>
    -- まず狭義順序を ≤ で書き換える
    dsimp [(· < ·), MyNat.lt] at *
    -- すると帰納法の仮定として ih : n = 0 ∨ 0 + 1 ≤ n が得られるが、
    -- どちらが成り立つかによって場合分けをする
    cases ih with
    | inl h =>
      -- n = 0 のときは明らか
      simp_all
    | inr h =>
      -- 0 + 1 ≤ n のときは n ≤ m → n ≤  m + 1 という性質を使えば示せる
      simp_all [MyNat.le_step]

/- 補題3 -/
theorem MyNat.eq_or_lt_of_le {m n : MyNat} : n ≤ m → n = m ∨ n < m := by
  intro h
  dsimp [(· < ·), MyNat.lt]
  rw [MyNat.le_iff_add] at *
  obtain ⟨k, hk⟩ := h
  induction k with
  | zero => simp_all
  | succ k ih =>
    have : ∃ k, n + 1 + k = m := by
      exists k
      rw [← hk]
      ac_rfl
    simp_all

/-- 狭義順序は広義順序よりも「強い」 -/
theorem MyNat.le_of_lt {a b : MyNat} (h : a < b) : a ≤ b := by
  -- < を ≤ で書き換える
  dsimp [(· < ·), MyNat.lt] at h
  have : a ≤ b := calc
    _ ≤ a + 1 := by simp
    _ ≤ b := by assumption
  assumption

theorem MyNat.le_of_eq_of_lt {m n : MyNat} : n = m ∨ n < m → n ≤ m := by
  intro h
  cases h with
  | inl h =>
    rw [h]
    simp -- 必要
  | inr h =>
    exact MyNat.le_of_lt h

/-- 広義順序 ≤ は等号 = と狭義順序 < で書き換えられる -/
theorem MyNat.le_iff_eq_or_lt {m n : MyNat} : n ≤ m ↔ n = m ∨ n < m := by
  constructor
  · apply MyNat.eq_or_lt_of_le
  · apply MyNat.le_of_eq_of_lt

/- 定理：a < b ∨ b ≤ a-/

theorem MyNat.lt_or_ge (a b : MyNat) : a < b ∨ b ≤ a := by
  -- a < b を定義に従い a + 1 ≤ b で書き換える
  dsimp [(· < ·), MyNat.lt]
  induction a with
  -- a = 0 のとき
  | zero =>
    -- このとき 1 ≤ b ∨ b ≤ 0 を示せば十分である
    suffices 1 ≤ b ∨ b ≤ 0 from by
      simp_all
    -- 任意の自然数は 0 か正であることから
    -- b は 0 か 1 以上である
    have : b = 0 ∨ 0 < b := MyNat.eq_zero_or_pos b
    dsimp [(· < ·), MyNat.lt] at this
    -- b = 0 → b ≥ 0 なので場合分けをすれば示せる
    cases this <;> simp_all
  | succ a ih =>
    cases ih with
    -- b ≤ a のとき
    | inr h =>
      -- b ≤ a + 1 を示せばよい
      -- これはすでに示した定理から従う
      right
      exact le_step h
    -- a + 1 ≤ b のとき
    | inl h =>
      -- このとき a + 1 = b または a + 1 < b のいずれかである
      simp [MyNat.le_iff_eq_or_lt] at h
      cases h with
      -- a + 1 = b の場合は順序の反射律に帰着でできる
      | inl h =>
        right
        simp_all
      -- a + 1 < b の場合は狭義順序の定義から従う
      | inr h =>
        left
        exact h
        /-- 教科書だと dsimp [(· < ·), MyNat.lt] at h; left; assumption -/

/- 系：a < b ↔ a ≤ b ∧ ¬ (b ≤ a) -/

theorem MyNat.lt_of_not_le {a b : MyNat} (h : ¬ (a ≤ b)) : b < a := by
  cases (MyNat.lt_or_ge b a) with
  | inl h => assumption
  | inr h => contradiction

theorem MyNat.not_le_of_lt {a b : MyNat} (h : a < b) : ¬ (b ≤ a) := by
  -- b ≤ a だと仮定して矛盾を示せばよい
  intro hle
  -- 見やすすさのために a < b の定義を展開しておく
  dsimp [(· < ·), MyNat.lt] at h
  -- また順序関係は和で書けるので書き換えておく
  rw [MyNat.le_iff_add] at *
  obtain ⟨k, hk⟩ := h
  obtain ⟨l, hl⟩ := hle
  -- このとき a + (k + l + 1) = a という等式が成り立つので
  -- k + l + 1 = 0 となるがこれはありえないので矛盾
  have : a + (k + l + 1) = a := calc
    _ = a + 1 + k + l := by ac_rfl
    _ = b + l := by rw [hk]
    _ = a := by rw [hl]
  simp at this

theorem MyNat.lt_iff_le_not_le {a b : MyNat} : a < b ↔ a ≤ b ∧ ¬ (b ≤ a) := by
  constructor <;> intro h
  case mp => simp_all [MyNat.not_le_of_lt, MyNat.le_of_lt]
  case mpr => simp_all [MyNat.lt_of_not_le]

/- 系：a ≤ b ∨ b ≤ a -/
theorem MyNat.le_total (a b : MyNat) : a ≤ b ∨ b ≤ a := by
  cases (MyNat.lt_or_ge a b) <;> simp_all [MyNat.le_of_lt]

/- 6.3.3 練習問題 -/
example (a : MyNat) : a ≠ a + 1 := by
  intro h
  have : 0 = 1 := by
    exact MyNat.add_left_cancel_iff.mp h
  simp at this

example (a : MyNat) : a ≠ a + 1 := by
  simp_all

example (n : MyNat) : ¬ (n + 1 ≤ n) := by
  apply MyNat.not_le_of_lt
  dsimp [(· < ·), MyNat.lt]
  apply MyNat.le_refl
