import LeanBook.NatOrder.DecidableOrd

/- 7.3 整数を作る -/

/- 7.3.1 MyNat を元に整数を構成する -/

/-- 自然数を　2 つペアにしたもの -/
abbrev PreInt := MyNat × MyNat

def PreInt.r (m n : PreInt) : Prop :=
  match m, n with
  | (m1, m2), (n1, n2) => m1 + n2 = m2 + n1

/-- 反射律 -/
theorem PreInt.r.refl : ∀ (m : PreInt), r m m := by
  intro (m1, m2)
  dsimp [r]
  ac_rfl

/-- 対称律 -/
theorem PreInt.r.symm : ∀ {m n : PreInt}, r m n → r n m := by
  intro (m1, m2) (n1, n2) h
  dsimp [r] at *
  have : n1 + m2 = n2 + m1 := calc
    _ = m2 + n1 := by ac_rfl
    _ = m1 + n2 := by rw [← h]
    _ = n2 + m1 := by ac_rfl
  exact this

/-- 推移律 -/
theorem PreInt.r.trans : ∀ {l m n : PreInt},
    r l m → r m n → r l n := by
  intro (l1, l2) (m1, m2) (n1, n2) hlm hmn
  dsimp [r] at *
  have : m1 + (l1 + n2) = m1 + (l2 + n1) := calc
    _ = m1 + n2 + l1 := by ac_rfl
    _ = m2 + n1 + l1 := by rw [hmn]
    _ = l1 + m2 + n1 := by ac_rfl
    _ = l2 + m1 + n1 := by rw [hlm]
    _ = m1 + (l2 + n1) := by ac_rfl
  simp_all

/-- PreInt.r は同値関係 -/
theorem PreInt.r.equiv : Equivalence r :=
  { refl := r.refl,
    symm := r.symm,
    trans := r.trans }

/-- PreInt 上の同値関係 -/
/- @[instance] def でなくて instance でも良い -/
@[instance] def PreInt.sr : Setoid PreInt := ⟨ r, r.equiv ⟩

/-- MyNat × MyNat を同値関係で割ることで構成した整数 -/
abbrev MyInt := Quotient PreInt.sr

/- 7.3.2 同値類のための記法を用意する -/
#check
  let a : PreInt := (1, 3)
  (Quotient.mk PreInt.sr a : MyInt)

#check
  let a : PreInt := (1, 3)
  Quotient.mk _ a

/-- 同値類を表す記法 -/
notation:arg (priority := low) "⟦" a:arg "⟧" => Quotient.mk _ a

-- 大分楽になった
#check (⟦(1, 3)⟧ : MyInt)

/- 7.3.3 数値リテラルが使えるようにする -/
def MyInt.ofNat  (n : Nat) : MyInt := ⟦(MyNat.ofNat n, 0)⟧

instance {n : Nat} : OfNat MyInt n where
  ofNat := MyInt.ofNat n

-- 数値リテラルが使えるようになった
#check (4 : MyInt)

#check_failure (-4 : MyInt) -- 負の数はまだ使えない

def PreInt.neg : PreInt → MyInt
  | (m, n) => ⟦(n, m)⟧

@[notation_simp]
theorem MyInt.sr_def (m n : PreInt) : m ≈ n ↔ m.1 + n.2 = m.2 + n.1 := by
  rfl

def MyInt.neg : MyInt → MyInt := Quotient.lift PreInt.neg <| by -- <| はパイプライン演算子
  -- PreInt.neg が同値関係を保つことを示したい
  -- (a1, a2) : PreInt と (b1, b2) : PreInt が同値だと仮定する
  intro (a1, a2) (b1, b2) hab
  -- このとき neg (a1, a2) と neg (b1, b2) も同値であることを示せばよいが
  -- 商空間における neg の定義より (a2, a1) と (b2, b1) が同値であることを示せばよい
  suffices (a2 + b1 = a1 + b2) from by
    dsimp [PreInt.neg]
    rw [Quotient.sound]
    assumption
  -- しかしこれは同値性の定義と仮定より明らか
  notation_simp at *
  simp_all

instance : Neg MyInt where
  neg := MyInt.neg

-- 後で使うので補題として登録しておく
@[simp]
theorem MyInt.neg_def (x y : MyNat) : - ⟦(x, y)⟧ = (⟦(y, x)⟧ : MyInt) := by
  dsimp [Neg.neg, MyInt.neg, PreInt.neg] -- なくても通る
  rfl

-- マイナス記号が使えるようになった
#check (-4 : MyInt)

-- 生のままだと使えないことに注意
#check_failure -4 -- failed to synthesize Neg MyNat

/- 7.3.4 練習問題 -/
-- r は α 上の二項関係とする
variable {α : Type} (r : α → α → Prop)

private theorem Ex.symm (refl : ∀ x, r x x) (h : ∀ x y z, r x y → r y z → r z x)
  : ∀ {x y : α}, r x y → r y x := by
  intro x y hxy
  apply (h _ _ _ hxy)
  apply refl

private theorem Ex.equiv (refl : ∀  x, r x x)
  (h : ∀ x y z, r x y → r y z → r z x) : Equivalence r := by
  constructor
  -- 反射律
  case refl =>
    intro x
    apply refl
  -- 対称律
  case symm =>
    intro x y hxy
    apply Ex.symm r refl h hxy
  -- 推移律
  case trans =>
    intro x y z hxy hyz
    apply Ex.symm r refl h (h x y z hxy hyz)
