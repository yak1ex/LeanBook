import LeanBook.NatCommMonoid.Induction

/- 4.3 等式変更による単純化を自動化する -/

/- 4.3.1 simpタクティクと[simp]属性 -/

example (n : MyNat) : 0 + (n + 0) = n := by
  -- 最初は simp で証明できない
  fail_if_success simp
  -- 明示的に rw で証明する
  rw [MyNat.add_zero, MyNat.zero_add]

attribute [simp] MyNat.add_zero MyNat.zero_add

example (n : MyNat) : 0 + (n + 0) = n := by
  -- simp で証明できるようになった
  simp

/-- MyNat においては zero だと解釈される -/
theorem MyNat.ctor_eq_zero : MyNat.zero = 0 := by rfl

example : MyNat.zero = 0 := by
  -- 手動で命題を渡すことで証明できる
  simp [MyNat.ctor_eq_zero]

-- 前節で証明した MyNat.add_succ を simp タクティクに登録する
attribute [simp] MyNat.add_succ

/- 4.3.2 at 構文 -/

example (m n : MyNat) (h : m + n + 0 = n + m) : m + n = n + m := by
  simp at h
  -- 仮定 h の形が変わった
  guard_hyp h : m + n = n + m
  rw [h]

example (m n : MyNat) (h : m + 0 = n) : (m + 0) + 0 = n := by
  simp at *
  -- 仮定とゴールの形が変わった
  guard_hyp h : m = n
  guard_target =ₛ m = n
  rw [h]

/- 4.3.3 simp_all -/

example (m n : MyNat) (h : m + 0 = n) : (m + 0) + 0 = n := by
  -- 一発で終了する
  simp_all

/- 4.3.4 @[simp] タグ -/
/-- 左のオペランドに付いた .succ は外側に出せる -/
@[simp] theorem MyNat.succ_add (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp [ih]

/- 4.3.5 simp? -/
example (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp? [ih] -- Try this: simp only [MyNat.add_succ, ih]

/- 4.3.6 calc で途中経過を明示する -/
example (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n with
  | zero => rfl
  -- n = n' のケースまで示せていたと仮定して、n = n' .succ のケースを示す
  | succ n' ih => calc
    _ = (m.succ + n').succ := by rw [MyNat.add_succ] -- 左辺を _ で省略するとゴールの左辺だと認識される
    _ = (m + n').succ.succ := by rw [MyNat.succ_add] -- 左辺は同じなので _ で省略できる
    _ = (m + n'.succ).succ := by rw [MyNat.add_succ]

example (n : MyNat) : 1 + n = n + 1 := calc
  _ = .succ 0 + n := by rfl                   -- 1 は定義から .succ 0 に等しい
  _ = .succ (0 + n) := by rw [MyNat.succ_add] -- .succ を外に出す
  _ = .succ n := by rw [MyNat.zero_add]       -- 0 + n = n を使って単純化
  _ = n + 1 := by rfl                         -- n + 1 は定義から .succ n に等しい

/- 4.3.7 練習問題 -/
example (n : MyNat) : 2 + n = n + 2 := by
  sorry
