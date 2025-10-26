/- 3.1 命題論理 -/

/- 3.1.1 命題 -/

#check Prop

-- これは命題
#check (1 + 1 = 3 : Prop)

-- これは命題ではなく、命題への関数
#check (fun n => n + 3 = 39 : Nat → Prop)

#check True
#check False

/-- Trueは何も主張していないので、何もなくても示せる -/
example : True := by trivial

/- 3.1.2 仮定を使う -/

example (P : Prop) (h : P) : P := by
  exact h

example (P : Prop) (h : P) : P := by
  assumption

/-- 矛盾からは何でも示せる -/
example (h : False) : ∀ x y z n : Nat,
  n ≥ 3 → x ^ n + y ^ n = z ^ n → x + y + z = 0 := by
  trivial

/- 3.1.3 含意(→) -/

example (P Q R : Prop) : (P → Q → R) = (P → (Q → R)) := by
  rfl

#eval True → True -- true
#eval True → False -- false
#eval False → True -- true
#eval False → False -- true

/-- いわゆるモーダスポネンス(三段論法) -/
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  -- P → Q が成り立つので、Qを示すにはPを示せばよい
  apply h
  -- Pの成立はわかっているので証明終わり
  apply hp

example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  exact h hp

/-- 含意の導入。Qであることがわかっているなら、仮定を足しても正しい -/
example (P Q : Prop) (hq : Q) : P → Q := by
  -- P → Q を示したいのでPであると仮定する
  intro hp
  -- 後はQを示せばよいが、これは仮定されていた
  exact hq

/- 3.1.4 否定(¬) -/

#eval ¬True -- false
#eval ¬False -- true

/-- Pと仮定すると矛盾する、ということは ¬P と等しい -/
example (P : Prop) : (¬ P) = (P → False) := by
  rfl

/-- Pと¬Pを同時に仮定すると矛盾する -/
example (P : Prop) (hnp : ¬ P) (hp : P) : False := by
  -- ¬P は P→False に等しいので、Pを示せばよい
  apply hnp
  -- 仮定 hp : P があるので証明終わり
  exact hp

/-- 対偶が元の命題と同値になることの、片方のケース -/
example (P Q : Prop) (h : P → ¬Q) : Q → ¬P := by
  -- Qならば¬Pを示したいのでQであったと仮定する
  intro hq
  -- ¬P は P→False に等しいので、
  -- さらにPであったと仮定する
  intro hp
  -- 仮定 h : P→Q→False に適用してFalseが得られる
  apply h hp hq

example (P : Prop) (hnp : ¬P) (hp : P) : False := by
  contradiction

example (P Q : Prop) (hnp : ¬P) (hp : P) : Q := by
  -- 矛盾を示せばよい
  exfalso
  -- 仮定に矛盾があるので証明終わり
  contradiction

/- 3.1.5 同値性(↔) -/

#eval True ↔ True -- true
#eval True ↔ False -- false
#eval False ↔ True -- false
#eval False ↔ False -- true

example (P Q : Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  constructor
  · apply h1
  · apply h2

example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  -- 両方向を示すことで証明する
  constructor
  -- まず左から右を示す
  case mp =>
    intro h
    exact h hq
  -- 右から左を示す
  case mpr =>
    intro hp hq
    exact hp

example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor <;> intro h
  case mp =>
    exact h hq
  case mpr =>
    intro hq
    exact h

example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by
  -- P ↔ Q が仮定にあるので、Pの代わりにQを示せばよい
  rw [h]
  -- 仮定 hq : Q があるので、証明終わり
  exact hq

example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  rw [← h]
  exact hp

/-- 同値な命題は等しい -/
example (P Q : Prop) (h : P ↔ Q) : P = Q := by
  rw [h]

/- 3.1.6 論理積(∧) -/

#eval True ∧ True -- true
#eval True ∧ False -- false
#eval False ∧ True -- false
#eval False ∧ False -- false

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  exact ⟨hp, hq⟩

example (P Q : Prop) (h : P ∧ Q) : P := by
  exact h.left

example (P Q : Prop) (h : P ∧ Q) : Q := by
  exact h.right

/- 3.1.7 論理和(∨) -/

#eval True ∨ True -- true
#eval True ∨ False -- true
#eval False ∨ True -- true
#eval False ∨ False -- false

example (P Q : Prop) (hp : P) : P ∨ Q := by
  left
  exact hp

example (P Q : Prop) (hq : Q) : P ∨ Q := by
  right
  exact hq

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp =>
    right
    exact hp
  | inr hq =>
    left
    exact hq

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h
  case inl hp =>
    right
    exact hp
  case inr hq =>
    left
    exact hq

/- 演習問題3.1.8 -/

example (P Q : Prop) : (¬P ∨ Q) → (P → Q) := by
  intro h pq
  cases h with
  | inl hnp => contradiction
  | inr hq => exact hq

example (P Q : Prop) : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro h
    constructor
    · intro hp
      apply h
      left
      exact hp
    · intro hq
      apply h
      right
      exact hq
  · intro h hpq
    cases hpq with
    | inl hp =>
      apply h.left
      exact hp
    | inr hq =>
      apply h.right
      exact hq
