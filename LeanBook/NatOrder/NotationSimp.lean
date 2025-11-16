import LeanBook.NatOrder.StrictOrder
import LeanBook.NatOrder.NotationSimpTag

/- 6.4 記法の展開を楽にする -/

/- 6.4.1 simp による方法 -/

theorem MyNat.lt_def (m n : MyNat) : m < n ↔ m + 1 ≤ n := by
  rfl

section
  /- ## simp で展開するテスト -/
  -- この section の中でのみ simp に登録する
  attribute [local simp] MyNat.lt_def
  example (m n : MyNat) : m < n := by
    simp
    -- 定義に展開された
    guard_target =ₛ m + 1 ≤ n
    sorry
end

/- 6.4.2 simp ラッパーを作成する -/
section

open Lean Parser Tactic

/-- + や ≤ など演算子や記法を定義に展開する -/
syntax "notation_simp" (simpArgs)? (location)? : tactic

macro_rules
| `(tactic| notation_simp $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic| simp only [notation_simp, $args,*] $[at $location]?)

end

-- < の定義を展開する定理に[notation_simp]属性を付与する
attribute [notation_simp] MyNat.lt_def

example (m n : MyNat) : m < n := by
  -- notaiton_simp が使える
  notation_simp
  -- 定義に展開された
  guard_target =ₛ m + 1 ≤ n
  sorry

example (m n : MyNat) (h : m < n) : m + 1 ≤ n := by
  -- rw タクティクや simp タクティクと同様の at 構文が使用できる
  notation_simp at *
  assumption

-- simp の挙動には変化がない
example (m n : MyNat) : m < n := by
  fail_if_success simp -- simp made no progress
  sorry

/- 6.4.3 notation_simp? を定義する -/
section

open Lean Parser Tactic

/-- + や ≤ など演算子や記法を定義に展開する -/
syntax "notation_simp?" (simpArgs)? (location)? : tactic

macro_rules
| `(tactic| notation_simp? $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic| simp? only [notation_simp, $args,*] $[at $location]?)

end
-- 展開に使用された定理を教えてくれる
example (m n : MyNat) : m < n := by
  notation_simp? -- Try this: simp only [MyNat.lt_def]
  sorry

/- 6.4.4 練習問題 -/
example (a b : MyNat) (h1 : a < b) (h2 : b < a) : False := by
  notation_simp at *
  rw [MyNat.le_iff_add] at *
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  have : a + (1 + k1 + 1 + k2) = a := calc
    _ = a + 1 + k1 + 1 + k2 := by ac_rfl
    _ = b + 1 + k2 := by rw [hk1]
    _ = a := by rw [hk2]
  simp at this
