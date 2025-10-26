/- 3.2 証明を楽にするコツ -/

/- 3.2.1 haveタクティクでローカルに補題を示す -/

/-- 三重否定の簡易化 -/
example (P: Prop) : ¬¬¬P → ¬P := by
  -- ¬¬¬P かつ P と仮定する
  intro hn3p hp
  -- ここで ¬¬P が成り立つ
  have hn2p : ¬¬ P := by
    -- なぜなら、¬P であると仮定したとき
    intro hnp
    -- 仮定の P と矛盾するから
    contradiction
  -- これで ¬¬¬P と ¬¬P が得られたが、これは矛盾である
  contradiction

example (P : Prop) : ¬¬¬P → ¬P := by
  intro hyn3p hp
  have : ¬¬P := by
    intro hnp
    contradiction
  -- this : ¬¬P という仮定が得られている
  guard_hyp this : ¬¬P
  contradiction

/- 3.2.2 sufficesタクティクでゴールを変更する -/
/-- 排中律の二重否定 -/
example (P : Prop) : ¬¬(P ∨ ¬P) := by
  -- ¬(P ∨ ¬P) と仮定する
  intro h
  -- ここで ¬P を示せば十分である
  suffices hyp : ¬P from by
    -- なぜなら、¬P が成り立つなら特に P∨¬P が成り立つので…
    have : P ∨ ¬P := by
      right
      exact hyp
    -- …最初の仮定と矛盾するから
    contradiction
  -- 無地ゴールを ¬P に帰着できた
  -- 以下、¬P を示す
  guard_target =ₛ ¬P
  -- Pであると仮定する
  intro hp
  -- このとき P∨¬P が成り立つ
  have : P ∨ ¬P := by
    left
    exact hp
  -- これは矛盾
  contradiction

/- 3.2.3 exact? タクティクでライブラリを検索する -/

example (P : Prop) : (P → True) ↔ True := by
  exact? -- Try this: exact imp_true_iff P

example (P : Prop) : (True → P) ↔ P := by
  exact? -- Try this: exact true_imp_iff

/- 3.2.4 show .. from 構文で一時的な補題を示す -/

example (P Q : Prop) (h : ¬P ↔ Q) : (P → False) ↔ Q := by
  rw [show (P → False) ↔ ¬ P from by rfl]
  rw [h]

/- 暗黙引数の自動束縛 {P} -/
example : P → P := by
  intro hp
  exact hp

/- 3.2.5 練習問題 -/

example (P : Prop) : ¬(P ↔ ¬P) := by
  intro h
  have hpnp : P → ¬P := by
    intro hp
    rw [← h]
    exact hp
  have hnp : ¬P := by
    intro hp
    apply hpnp hp
    exact hp
  have hp : P := by
    rw [h]
    exact hnp
  contradiction
