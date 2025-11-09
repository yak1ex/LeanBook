import LeanBook.NatCommMonoid.AcRfl

/- 4.5 帰納法を改善する -/

/- 4.5.1 帰納法で記法が崩れる問題 -/
example (m n : MyNat) : m + n = n + m := by
  induction n with
  | zero =>
    -- ゴールに MyNat.zero が現れてしまう
    -- 見づらいので m + 0 = 0 + m になってほしい
    guard_target =ₛ m + MyNat.zero = MyNat.zero + m
    simp [MyNat.ctor_eq_zero]
  | succ n ih =>
    -- ゴールに MyNat.succ n が現れてしまう
    -- これも m + (n + 1) = (n + 1) + m になってほしい
    guard_target =ₛ m + MyNat.succ n = MyNat.succ n + m
    simp [ih]

/- 4.5.2 Lean における帰納法の仕組み -/
#check MyNat.rec -- MyNat.rec.{u}

/- 4.5.3 帰納法で記法が崩れるのを防ぐ -/
/-- MyNat 用の帰納法の原理を書き直したもの -/
def MyNat.recAux.{u} {motive : MyNat → Sort u}
  (zero : motive 0)
  (succ : (n :MyNat) → motive n → motive (n + 1)) (t : MyNat) : motive t :=
  match t with
  | .zero => zero
  | .succ n => succ n (MyNat.recAux zero succ n)

  attribute [induction_eliminator] MyNat.recAux

  example (m n : MyNat) : m + n = n + m := by
    induction n with
    | zero =>
      -- ゼロになっている！
      guard_target =ₛ m + 0 = 0 + m
      simp
    | succ n ih =>
      -- (· + 1) と表記されている！
      guard_target =ₛ m + (n + 1) = (n + 1) + m
      ac_rfl

/- 4.5.4 練習問題 -/
/-- 「1つ前」の自然数を返す関数。0 に対しては 0 を返すことに注意 -/
private def MyNat.pred (n : MyNat) : MyNat :=
  match n with
  | 0 => 0
  | n + 1 => n

example (n : MyNat) : MyNat.pred (MyNat.pred n + 1) = MyNat.pred n := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    rfl

/- 練習問題の追加あり -/
