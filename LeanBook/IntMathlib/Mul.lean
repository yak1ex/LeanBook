import LeanBook.IntMathlib.Add

/- 8.4 整数は環 -/

/- 8.4.1 自然数が半環であることを再利用可能にする -/

/- MyNat を可換なモノイドとして登録する -/
/-- 単位元が何であるかを指定する -/
instance : Zero MyNat where
  zero := 0

instance : AddCommMonoid MyNat where
  zero_add := MyNat.zero_add
  add_zero := MyNat.add_zero
  add_assoc := MyNat.add_assoc
  add_comm := MyNat.add_comm
  nsmul := nsmulRec

/- MyNat を半環として登録する -/
/-- 掛け算の単位元を指定する -/
instance : One MyNat where
  one := 1

/-- MyNat は可換な半環 -/
instance : CommSemiring MyNat where
  left_distrib := MyNat.mul_add
  right_distrib := MyNat.add_mul
  zero_mul := MyNat.zero_mul
  mul_zero := MyNat.mul_zero
  mul_one := MyNat.mul_one
  one_mul := MyNat.one_mul
  mul_assoc := MyNat.mul_assoc
  mul_comm := MyNat.mul_comm

example (a b c : MyNat) : (a + b) * (a + c) = a * a + (b + c) * a + b * c := by
  -- 分配法則や交換法則を自動で使って証明をしてくれるようになった
  ring

/- 8.4.2 掛け算の定義 -/
def PreInt.mul (m n : PreInt) : MyInt :=
  match m, n with
  | (m1, m2), (n1, n2) => ⟦(m1 * n1 + m2 * n2, m1 * n2 + m2 * n1)⟧

/-- 整数の掛け算 -/
def MyInt.mul : MyInt → MyInt → MyInt := Quotient.lift₂ PreInt.mul <| by
  intro (a, b) (c, d) (p, q) (r, s) h1 h2
  dsimp [PreInt.mul]
  apply Quot.sound
  notation_simp at *

  -- 長いので左辺と右辺をぞれぞれ変数におく
  generalize hl : a * c + b * d + (p * s + q * r) = lhs
  generalize hr : a * d + b * c + (p * r + q * s) = rhs

  -- ひたすら計算する
  have leml : lhs + q * c = c * b + b * d + d * p + p * r + r * q := calc
    _ = a * c + b * d + (p * s + q * r) + q *c := by rw[hl]
    _ = (a + q) * c + b * d + p * s + q * r := by ring
    _ = (b + p) * c + b * d + p * s + q * r := by rw[h1]
    _ = b * c + b * d + q * r + p * (c + s) := by ring
    _ = b * c + b * d + q * r + p * (d + r) := by rw[h2]
    _ = c * b + b * d + d * p + p * r + r * q := by ring

  have lemr : rhs + q * c = c * b + b * d + d * p + p * r + r * q := calc
    _ = a * d + b * c + (p * r + q * s) + q * c := by rw[hr]
    _ = a * d + b * c + p * r + q * (c + s) := by ring
    _ = a * d + b * c + p * r + q * (d + r) := by rw[h2]
    _ = (a + q) * d + b * c + p * r + q * r := by ring
    _ = (b + p) * d + b * c + p * r + q * r := by rw[h1]
    _ = c * b + b * d + d * p + p * r + r * q := by ring

  have lem : lhs + q * c = rhs + q * c := by rw[leml, lemr]
  simp_all

instance : Mul MyInt where
  mul := MyInt.mul

/- 8.4.3 1や0の掛け算 -/

@[notation_simp]
theorem MyNat.toMyNat_one : MyNat.ofNat 1 = 1 := rfl

@[simp]
theorem MyInt.mul_one (m : MyInt) : m * 1 = m := by
  revert m
  unfold_int₁
  ring

@[simp]
theorem MyInt.one_mul (m : MyInt) : 1 * m = m := by
  revert m
  unfold_int₁
  ring

@[simp]
theorem MyInt.mul_zero (m : MyInt) : m * 0 = 0 := by
  revert m
  unfold_int₁

@[simp]
theorem MyInt.zero_mul (m : MyInt) : 0 * m = 0 := by
  revert m
  unfold_int₁
  ring

/- 8.4.4 交換法則、結合法則、分配法則 -/

theorem MyInt.mul_comm (m n : MyInt) : m * n = n * m := by
  revert m n
  unfold_int₂
  ring

theorem MyInt.mul_assoc (m n k : MyInt) : (m * n) * k = m * (n * k) := by
  revert m n k
  unfold_int₃
  ring

theorem MyInt.left_distrib (m n k : MyInt) : m * (n + k) = m * n + m * k := by
  revert m n k
  unfold_int₃
  ring

theorem MyInt.right_distrib (m n k : MyInt) : (m + n) * k = m * k + n * k := by
  revert m n k
  unfold_int₃
  ring

/- 8.4.5 ring タクティクで再利用可能にする -/

instance : CommRing MyInt where
  left_distrib := MyInt.left_distrib
  right_distrib := MyInt.right_distrib
  zero_mul := MyInt.zero_mul
  mul_zero := MyInt.mul_zero
  mul_one := MyInt.mul_one
  one_mul := MyInt.one_mul
  mul_assoc := MyInt.mul_assoc
  mul_comm := MyInt.mul_comm
  zsmul := zsmulRec
  neg_add_cancel := MyInt.neg_add_cancel

example (m n : MyInt) : (m - n) * (m + n) = m * m - n * n := by
  -- 整数に対しても ring タクティクが使えるようになった
  ring

/- 8.4.6 練習問題 -/

example (m : MyInt) : ∃ s t : MyInt, s * t = m * m * m - 1 := by
  exists (m - 1), (m * m + m + 1)
  ring
