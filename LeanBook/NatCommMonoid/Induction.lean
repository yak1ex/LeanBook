import LeanBook.NatCommMonoid.TypeClass

/- 4.2 帰納法で 0+n=n を証明する -/

/- 4.2.1 rfl を試す -/
/-
example (n : MyNat) : 0 + n = n := by
  rfl
-/

/- 4.2.2 rfl で証明できない理由 -/
-- "fun n => n" というシンプルな式が表示される
#reduce fun (n: MyNat) => n + 0
-- 複雑な式が表示される
#reduce fun (n : MyNat) => 0 + n

/- 4.2.3 induction タクティクで帰納法 -/
-- infoview における表示の仕方を制御するための設定
set_option pp.fieldNotation.generalized false in

example (n: MyNat) : 0 + n = n := by
  -- n についての帰納法で証明する
  induction n with
  -- n = 0 のケース
  | zero =>
    -- ゴールが ⊢ 0 + MyNat.zero = MyNat.zero という形になる
    guard_target =ₛ 0 + MyNat.zero = MyNat.zero
    -- 変数がないので rfl で証明できる
    -- このケースは証明終わり
    rfl
  -- n = succ n' のケース
  | succ n' ih =>
    -- ゴールが ⊢ 0 + MyNat.succ n' = MyNat.succ n' という形になる
    guard_target =ₛ 0 + MyNat.succ n' = MyNat.succ n'
    -- 帰納法の仮定 ih が手に入る
    guard_hyp ih : 0 + n' = n'
    sorry

example (n: MyNat) : 0 + n = n := by
  induction n
  case zero =>
    rfl
  case succ n' ih =>
    sorry

/- 4.2.4 rwタクティクで等式置換 -/
/-- 0 を右から足しても変わらない -/
theorem MyNat.add_zero (n : MyNat) : n + 0 = n := by rfl

example (m n : MyNat) : (n + 0) + m = n + m := by
  rw [MyNat.add_zero]

/-- add_zero の等式の順序が逆のバージョン -/
theorem MyNat.add_zero_rev (n : MyNat) : n = n + 0 := by rfl

example (m n : MyNat) : (n + 0) + m = n + m := by
  rw [← MyNat.add_zero_rev]

example (m n : MyNat) (h : m + 0 = n) : n + m = m + n := by
  -- 仮定の h を簡略化して m = n を得る
  rw [MyNat.add_zero] at h
  rw [h]

/- 4.2.5 証明を完成させる -/

/-- 右のオペランドに付いた .succ は外側に出せる -/
theorem MyNat.add_succ (m n : MyNat) : m + .succ n = .succ (m + n) := by
  rfl

/-- 0 を左から足しても変わらない -/
theorem MyNat.zero_add (n : MyNat) : 0 + n = n := by
  induction n with
  -- n = 0 のケース
  | zero =>
    rfl
  -- n = succ n' のケース
  | succ n' ih =>
    -- 両辺の外側に .succ を持ってくる
    rw [MyNat.add_succ]
    rw [ih]

/- 4.2.6 練習問題 -/
example (n : MyNat) : 1 + n = .succ n := by
  sorry
