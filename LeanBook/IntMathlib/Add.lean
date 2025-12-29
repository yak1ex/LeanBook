import LeanBook.Int.Basic
import Mathlib.Tactic

/- 8.3 整数が足し算に関してアーベル群であることを利用する -/

/- 8.3.1 整数の足し算を定義する -/

def PreInt.add (m n : PreInt) : MyInt :=
  match m, n with
  | (m1, m2), (n1, n2) => ⟦(m1 + n1, m2 + n2)⟧

  /-- 整数の足し算 -/
def MyInt.add : MyInt → MyInt → MyInt := Quotient.lift₂ PreInt.add <| by
  intro (m1, m2) (n1, n2) (m'1, m'2) (n'1, n'2) rm rn
  dsimp [PreInt.add]
  apply Quotient.sound
  notation_simp at *

  have : m1 + n1 + (m'2 + n'2) = m2 + n2 + (m'1 + n'1) := calc
    _ = (m1 + m'2) + (n1 + n'2) := by ac_rfl
    _ = (m2 + m'1) + (n2 + n'1) := by rw[rm, rn]
    _ = m2 + n2 + (m'1 + n'1) := by ac_rfl
  assumption

instance instAddMyInt : Add MyInt where
  add := MyInt.add

-- 足し算が使えるようになった
#check (3 + 4 : MyInt)

@[simp]
theorem MyInt.add_def (x1 x2 y1 y2 : MyNat)
  : ⟦(x1, y1)⟧ + ⟦(x2, y2)⟧ = (⟦(x1 + x2, y1 + y2)⟧ : MyInt) := by
  dsimp [(· + ·), Add.add, MyInt.add, PreInt.add]

/- 8.3.2 足し算と0 -/

-- notation_simp で簡単に展開できるようにする
attribute [notation_simp] PreInt.sr PreInt.r

-- notation_simp に使用させるための補題
@[notation_simp, simp] theorem MyNat.ofNat_zero : MyNat.ofNat 0 = 0 := rfl

@[simp]
theorem MyInt.add_zero (m : MyInt) : m + 0 = m := by
  -- m : MyInt の代表元 a : PreInt を考えると
  -- ∀  (a : PreInt), ⟦a⟧ + 0 = ⟦a⟧ を示せば良い
  refine Quotient.inductionOn m ?_

  -- a : PreInt が与えられたとし a = (a1, a2) と表されたとする
  intro (a1, a2)

  -- このとき同値関係の定義から
  -- a1 + 0 + a2 = a2 + 0 + a1 を示せばよい
  apply Quot.sound
  notation_simp

  -- これは自然数の交換法則から従う
  ac_rfl

@[simp]
theorem MyInt.zero_add (m : MyInt) : 0 + m = m := by
  refine Quotient.inductionOn m ?_
  intro (a1, a2)
  apply Quot.sound
  notation_simp
  ac_rfl

section
  local macro "unfold_int₁" : tactic => `(tactic| focus
    refine Quotient.inducitonOn m ?_
    intro (a1, a2)
    apply Quot.sound
    notation_simp
  )

  example (m : MyInt) : m + 0 = m := by
    -- 証明が通らない
    fail_if_success unfold_int₁ -- unknown constant 'Quotient.inducitonOn'
    sorry
end

section
  -- マクロ衛生を無効にする
  set_option hygiene false

  local macro "unfold_int₁" : tactic => `(tactic| focus
    refine Quotient.inductionOn m ?_
    intro (a1, a2)
    apply Quot.sound
    notation_simp
  )

  example (m : MyInt) : m + 0 = m := by
    -- 今度は証明が通る
    unfold_int₁
    ac_rfl
end

/-- 整数に関する命題を自然数の話に帰着させる(1変数用) -/
macro "unfold_int₁" : tactic => `(tactic| focus
  intro m -- intro で m を導入する
  refine Quotient.inductionOn m ?_
  intro (a1, a2)
  apply Quot.sound
  notation_simp
)

example (m : MyInt) : m + 0 = m := by
  revert m -- revert でゴールを ∀ m, m + 0 = m にする
  unfold_int₁
  ac_rfl

example (m : MyInt) : 0 + m = m := by
  revert m -- revert でゴールを ∀ m, 0 + m = m にする
  unfold_int₁
  ac_rfl

/- 8.3.3 足し算の結合法則と交換法則を示す -/

/-- 整数に関する命題を自然数の話に帰着させる(2変数用) -/
macro "unfold_int₂" : tactic => `(tactic| focus
  intro m n
  refine Quotient.inductionOn₂ m n ?_
  intro (a1, a2) (b1, b2)
  apply Quot.sound
  notation_simp
)

/-- 整数に関する命題を自然数の話に帰着させる(3変数用) -/
macro "unfold_int₃" : tactic => `(tactic| focus
  intro m n k
  refine Quotient.inductionOn₃ m n k ?_
  intro (a1, a2) (b1, b2) (c1, c2)
  apply Quot.sound
  notation_simp
)

theorem MyInt.add_assoc (m n k : MyInt) : m + n + k = m + (n + k) := by
  revert m n k
  unfold_int₃
  ac_rfl

theorem MyInt.add_comm (m n : MyInt) : m + n = n + m := by
  revert m n
  unfold_int₂
  ac_rfl

-- MyInt の足し算が結合法則を満たすことを登録する
instance : Std.Associative (α := MyInt) (· + ·) where
  assoc := MyInt.add_assoc

-- MyInt の足し算が交換法則を満たすことを登録する
instance : Std.Commutative (α := MyInt) (· + ·) where
  comm := MyInt.add_comm

/- 8.3.4 整数の引き算を定義する -/

/-- 整数の引き算 -/
def MyInt.sub (m n : MyInt) : MyInt := m + -n

/-- 引き算 a - b と書けるように型クラスに定義する -/
instance : Sub MyInt where
  sub := MyInt.sub

-- 後で使うので補題として登録しておく
@[simp, notation_simp]
theorem MyInt.sub_def (x y : MyInt) : x - y = x + -y := rfl

theorem MyInt.neg_add_cancel (m : MyInt) : -m + m = 0 := by
  revert m
  unfold_int₁
  ac_rfl

/- 8.3.5 abel タクティクで再利用可能にする -/

/-- 整数は足し算に関して可換な環 -/
instance : AddCommGroup MyInt where
  add_assoc := MyInt.add_assoc
  add_comm := MyInt.add_comm
  zero_add := MyInt.zero_add
  add_zero := MyInt.add_zero
  neg_add_cancel := MyInt.neg_add_cancel
  nsmul := nsmulRec -- 自然数によるスカラー倍
  zsmul := zsmulRec -- 整数によるスカラー倍

-- abel タクティクは引き算を扱える
example (a b : MyInt) : (a + b) - b = a := by
  abel

/- 8.3.6 練習問題 -/
example (a b c : MyInt) : (a - b) - c + b + c = a := by
  abel
