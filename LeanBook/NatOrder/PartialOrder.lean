import LeanBook.NatOrder.OrdMonoid

/- 6.6 a ≤ b → b ≤ a → a = b -/

/- 6.6.1 狭義順序と広義順序の推移律 -/
variable {m n k : MyNat}

theorem MyNat.lt_trans (h1 : n < m) (h2 : m < k) : n < k := by
  notation_simp at *
  have : n + 1 ≤ k := calc
    _ ≤ m := by exact h1
    _ ≤ m + 1 := by simp
    _ ≤ k := by exact h2
  assumption

theorem MyNat.lt_of_le_of_lt (h1 : n ≤ m) (h2 : m < k) : n < k := by
  notation_simp at *
  have : n + 1 ≤ k := calc
    _ ≤ m + 1 := by compatible
    _ ≤ k := by exact h2
  assumption

theorem MyNat.lt_of_lt_of_le (h1 : n < m) (h2 : m ≤ k) : n < k := by
  notation_simp at *
  have : n + 1 ≤ k := calc
    _ ≤ m := by exact h1
    _ ≤ k := by exact h2
  assumption

instance : Trans (· < · : MyNat → MyNat → Prop) (· < ·) (· < ·) where
  trans := MyNat.lt_trans

instance : Trans (· ≤ · : MyNat → MyNat → Prop) (· < ·) (· < ·) where
  trans := MyNat.lt_of_le_of_lt

instance : Trans (· < · : MyNat → MyNat → Prop) (· ≤ ·) (· < ·) where
  trans := MyNat.lt_of_lt_of_le

/- 6.6.2 狭義順序の非反射律 -/
@[simp]
theorem MyNat.lt_irrefl (n : MyNat) : ¬ (n < n) := by
  intro h
  notation_simp at h
  rw [MyNat.le_iff_add] at *
  obtain ⟨k, hk⟩ := h
  have : n + (k + 1) = n := calc
    _ = n + 1 + k := by ac_rfl
    _ = n := by rw [hk]
  simp_all

/- 6.6.3 反対称律 -/
theorem MyNat.le_antisymm (h1 : n ≤ m) (h2 : m ≤ n) : n = m := by
  induction h1 with
  | refl => rfl
  | @step m h ih =>
    have : n < n := calc
      _ ≤ m := by exact h
      _ < m + 1 := by notation_simp; simp /- rfl だと通らなかった -/
      _ ≤ n := by exact h2
    simp at this

/- 6.6.4 練習問題 -/
example (a b : MyNat) : a < b ∨ a = b → a ≤ b := by
  intro h
  cases h with
  | inl hab => apply MyNat.le_of_lt hab
  | inr hab => rw [hab]; apply MyNat.le_refl -- なくても通るはずなのだが……
