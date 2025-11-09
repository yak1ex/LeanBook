/- 3.7 依存型 -/

/- 3.7.1 全称量化 -/
#check Nat.add_zero -- Nat.add_zero (n : Nat) : n + 0 = n

#check Nat.add_zero 0 -- Nat.add_zero 0 : 0 + 0 = 0

#check Nat.add_zero 42 -- Nat.add_zero 42 : 42 + 0 = 42

#check (Nat.add_zero : (n : Nat) → n + 0 = n) -- Nat.add_zero : ∀ (n : Nat), n + 0 = n

example : (∀ n : Nat, n + 0 = n) = ((n : Nat) → n + 0 = n) := by
  rfl

set_option pp.foralls false in
#check (∀ n : Nat, n + 0 = n) -- (n : Nat) → n + 0 = n : Prop

/- 3.7.2 ベクトル -/
/-
inductive List (α : Type) : Type where
  /-- カラリストは連結リスト -/
  | nil
  /-- 連結リスト l : List α の先頭に a : α を追加することで新しい連結リストが得られる -/
  | cons (a : α) (l : List α)
-/

example : List Nat := [0, 1, 2, 3]
example : List Nat := [0, 1]

inductive Vect (α : Type) : Nat → Type where
  /-- 空ベクトルは長さ 0 のベクトル -/
  | nil : Vect α 0
  /-- ベクトル v : Vect α n の先頭に a : α を追加することで新しいベクトルが得られる -/
  | cons (a : α) {n : Nat} (v : Vect α n) : Vect α (n + 1)

example : Vect Nat 0 := Vect.nil
example : Vect Nat 1 := Vect.cons 42 Vect.nil

/- 3.7.3 依存ペア -/
example : (α : Type) × α := ⟨Nat, 1⟩
example : (α : Type) × α := ⟨Bool, true⟩
example : (α : Type) × α := ⟨Prop, True⟩

example : List ((α : Type) × α) := [⟨Nat, 1⟩, ⟨Bool, true⟩, ⟨Prop, True⟩]

/- 3.7.4 練習問題 -/
example : List ((α : Type) × α) := [⟨Nat, 42⟩, ⟨Bool, false⟩]

example : {α : Type} → {n : Nat} → (a : α) → (v : Vect α n) →
  Vect α (n + 1) :=
  fun a v => (Vect.cons a v)
