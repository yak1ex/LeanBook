/- 3.6 カリー・ハワード同型対応 -/

/- 3.6.1 証明とプログラムは同じもの -/
/-- 1 + 1 = 2 という命題の証明 -/
theorem one_add_one_eq_two : 1 + 1 = 2 := by
  rfl

#check one_add_one_eq_two -- one_add_one_eq_two : 1 + 1 = 2

#check (by rfl : 1 + 1 = 2) -- (Eq.refl (1 + 1) : 1 + 1 = 1 + 1)

/- 3.6.2 P → Q の証明は関数 -/
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  exact h hp

/- 3.6.3 タクティクの招待 -/
/-- Nat 上の恒等関数 -/
def idOnNat : Nat → Nat := by? -- Try this: fun n => n
  intro n
  exact n

#eval idOnNat 42 -- 42

/- 3.6.4 練習問題 -/
example (P Q : Prop) (hp : P) : Q → P :=
  (fun _ => hp)
