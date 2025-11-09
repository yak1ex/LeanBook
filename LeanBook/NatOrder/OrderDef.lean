import LeanBook.NatOrder.AddCancel

/- 6.2 順序を定義する -/

/- 6.2.1 順序関係を帰納的に定義する -/
/-- 自然数上の講義の順序関係 -/
inductive MyNat.le (n : MyNat) : MyNat → Prop
  /-- ∀ n, n ≤ n -/
  | refl : MyNat.le n n
  /-- n ≤ m ならば n ≤ m + 1 -/
  | step {m : MyNat} : MyNat.le n m → MyNat.le n (m + 1)

/-- MyNat.le を ≤ で表せるようにする -/
instance : LE MyNat where
  le := MyNat.le

/- 6.2.2 帰納型では帰納法が使える -/
example (m n : MyNat) (P : MyNat → MyNat → Prop) (h : m ≤ n) : P m n := by
  induction h with
  | refl =>
    -- P m m を示す
    -- m = n の場合
    guard_target =ₛ P m m
    sorry
  | @step n h ih =>
    -- P m n → P m (n + 1) を示す
    guard_hyp ih : P m n
    guard_target =ₛ P m (n + 1)
    sorry

@[induction_eliminator]
def MyNat.le.recAux {n b : MyNat}
    {motive : (a : MyNat) → n ≤ a → Prop}
    (refl : motive n MyNat.le.refl)
    (step : ∀ {m : MyNat} (a : n ≤ m),
      motive m a → motive (m + 1) (MyNat.le.step a))
    (t : n ≤ b) :
  motive b t := by
  induction t with
  | refl => exact refl
  | @step c h ih =>
    exact step (a := h) ih

/- 6.2.3 反射率と推移律を示す -/
/-- 反射率 -/
theorem MyNat.le_refl (n : MyNat) : n ≤ n := by
  exact MyNat.le.refl

-- m, n, k は MyNat の項とする
variable {m n k : MyNat}

theorem MyNat.le_step (h : n ≤ m) : n ≤ m + 1 := by
  apply MyNat.le.step
  exact h

/-- 推移律 -/
theorem MyNat.le_trans (hnm : n ≤ m) (hmk : m ≤ k) : n ≤ k := by
  -- 順序関係を帰納的に定義したので順序に対する帰納法ができる
  induction hmk with
  | refl => exact hnm
  | @step k hmk ih =>
    exact MyNat.le.step ih

attribute [refl] MyNat.le.refl

theorem MyNat.le_add_one_right (n : MyNat) : n ≤ n + 1 := by
  apply MyNat.le.step
  -- rfl で示せる
  rfl

/-- MyNat.le を「推移的な二項関係」として定義する -/
instance : Trans (· ≤ · : MyNat → MyNat → Prop) (· ≤ ·) (· ≤ ·) where
  trans := MyNat.le_trans

-- calc が使えるようになった！
theorem MyNat.le_add_one_left (n : MyNat) : n ≤ 1 + n := calc
  _ ≤ n + 1 := by apply le_add_one_right
  _ = 1 + n := by ac_rfl

attribute [simp] MyNat.le_refl MyNat.le_add_one_right MyNat.le_add_one_left
