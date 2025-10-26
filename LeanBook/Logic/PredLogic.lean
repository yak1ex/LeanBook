/- 3.3 述語論理 -/

/- 3.3.1 全称量化(∀) -/

/-- (Leanの標準の)自然数上の述語 -/
def P (n : Nat) : Prop := n = n

example : ∀ a : Nat, P a := by
  -- x : Nat が任意に与えられたとする
  intro x
  -- Pを展開すればあきらか
  dsimp [P]

/-- すべての自然数 x について P x が成り立つなら、 P 0 も成り立つ -/
example (P : Nat → Prop) (h : ∀ x : Nat, P x) : P 0 := by
  -- h を 0 に適用すればあきらか
  apply h 0

/- 3.3.2 存在量化(∃) -/

/-- 偶数であることを表す述語 -/
def Even (n : Nat) : Prop := ∃ m : Nat, n = m + m

/-- 4: Nat は偶数 -/
example : even 4 := by
  exists 2

example (α : Type) (P Q : α → Prop) (h : ∃ x : α, P x ∧ Q x)
  : ∃ x : α, Q x := by
  -- 仮定 h が存在を主張している y を取り出す
  obtain ⟨y, hy⟩ := h
  -- この y が求めるものである
  exists y
  -- なぜなら、 P y ∧ Q y が成り立つから
  exact hy.right

/- 3.3.3 具体例 -/

/-- 人間たちの集合 -/
opaque Human : Type

/-- 愛の関係 -/
opaque Love : Human → Human → Prop

-- 専用の中置記法を用意する
@[inherit_doc] infix:50 " -♥→ " => Love

/-- すべての人に愛されているアイドルが存在する -/
def IdolExists : Prop := ∃ idol : Human, ∀ h : Human, h -♥→ idol

/-- 誰にでも好きな人の一人くらいいる -/
def EveryoneLovesSomeone : Prop := ∀ h : Human, ∃ loved : Human, h -♥→ loved

#check ∃ philan : Human, ∀ h : Human, philan -♥→ h

def PhilanExists : Prop := ∃ philan : Human, ∀ h : Human, philan -♥→ h

#check ∀ h : Human, ∃ lover : Human, lover -♥→ h

def EveryoneLoved : Prop := ∀ h : Human, ∃ lover : Human, lover -♥→ h

example : PhilanExists → EveryoneLoved := by
  -- 博愛主義主義者の存在を仮定する
  intro h
  -- 存在が主張されている博愛主義者を philan とする
  -- このとき定義から h : ∀ h : Human, philan -♥→ h が成り立つ
  obtain ⟨philan, h⟩ := h
  -- このとき EveryoneLoved を示したい
  -- 定義より ∀ h : Human, ∃ lover : Human, lover -♥→ h を示せばよい
  dsimp [EveryoneLoved]
  -- そこで任意に human : Human が与えられたと仮定する
  intro human
  -- ここで ∃ loever : Human, lover -♥→ human を示したいが、
  -- lover = philan とすればよい
  exists philan
  -- なぜなら philan -♥→ human が成り立つからである
  -- これで示すべきことが示せた
  exact h human

/- 3.3.4 練習問題 -/

example : IdolExists → EveryoneLovesSomeone := by
  dsimp [IdolExists, EveryoneLovesSomeone]
  intro h
  obtain ⟨idol, hidol⟩ := h
  intro human
  exists idol
  exact hidol human
