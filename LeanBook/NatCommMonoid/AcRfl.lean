import LeanBook.NatCommMonoid.Simp

/- 4.4 足し算の交換法則と結合法則を解放する -/

/- 4.4.1 交換法則と結合法則を「示す」 -/

/-- 足し算の交換法則 -/
theorem MyNat.add_comm (m n : MyNat) : m + n = n + m := by
  induction n with
  | zero =>
    simp [MyNat.ctor_eq_zero]
  | succ n ih =>
    simp [ih]

/-- 足し算の結合法則 -/
theorem MyNat.add_assoc (l m n : MyNat) : l + m + n = l + (m + n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [ih]

/- 4.4.2 交換法則と結合法則を「利用する」 -/
example (l m n : MyNat) : l + m + n + 3 = m + (l + n) + 3 := calc
  -- 引数を指定することで、どの変数同士を交換するか指定できる
  _ = m + l + n + 3 := by rw [MyNat.add_comm l m]
  _ = m + (l + n) + 3 := by rw [MyNat.add_assoc m l n]

-- MyNat の足し算が結合法則を満たすことを登録する
instance : Std.Associative (α := MyNat) (· + ·) where
  assoc := MyNat.add_assoc

-- MyNat の足し算が交換法則を満たすことを登録する
instance : Std.Commutative (α := MyNat) (· + ·) where
  comm := MyNat.add_comm

example (l m n : MyNat) : l + m + n + 3 = m + (l + n) + 3 := by
  ac_rfl

/- 4.4.3 練習問題 -/
example (l m n : MyNat) : l + (1 + m) + n = m + (l + n) + 1 := by
  ac_rfl
