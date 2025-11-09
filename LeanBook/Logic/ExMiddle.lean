/- 3.4 排中律と直観主義論理 -/

/- 3.4.1 Leanは直観主義論理　-/

/- 3.4.2 Leanで排中律を使う -/

/-- 二重否定の除去 -/
example (P: Prop) : ¬¬P → P := by
  -- ¬¬P だと仮定する
  intro hh2p
  -- 排中律より、P ∨ ¬P が成り立つ
  by_cases h : P
  -- P が成り立つ場合は即座に証明が終了する
  · exact h
  -- P が成り立たない場合、¬¬P という仮定と矛盾する
  · contradiction

/- 3.4.3 練習問題 -/
/-- 二重否定の除去 -/
example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases p : P
  · exact p
  · contradiction

/-- ド・モルガンの法則 -/
example (P Q : Prop) : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro h
    by_cases p : P
    · right
      intro q
      apply h
      constructor
      · exact p
      · exact q
    · left
      exact p
  · intro h
    cases h with
    | inl hnp =>
      intro hpq
      exact hnp hpq.left
    | inr hnq =>
      intro hpq
      exact hnq hpq.right

/-- 対偶が元の命題と同値であること -/
example (P Q : Prop) : (P → Q) ↔ (¬Q → ¬P) := by
  constructor
  · intro hpq hnq p
    apply hnq (hpq p)
  · intro hnqnp p
    by_cases hq : Q
    · exact hq
    · exfalso
      exact ((hnqnp hq) p)
