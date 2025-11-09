/- 3.5 選択原理 -/

/- 3.5.1 公理の追跡 -/

#check Classical.em

#print axioms Classical.em

#check propext
#check Quot.sound

/- 3.5.2 選択原理 -/

#check Classical.choice

/- 3.5.3 計算可能性 -/

/-- 関数の全射性 -/
def Surjective {X Y : Type} (f : X → Y) : Prop :=
  ∀ y : Y, ∃ x : X, f x = y

/-- Surjective を使用する例：恒等関数は全射 -/
example : Surjective (fun x : Nat => x) := by
  intro y
  exists y


variable (X Y : Type)

/-- 全射であるような関数 f : X → Y に対して、
    その右逆関数 g : Y → X を返すような高階関数 -/
noncomputable def inverse (f : X → Y) (hf : Surjective f) : Y → X := by
  -- y : Y が与えられたとする
  intro y
  -- f は全射なので {x // f x = y} は空でない
  have : Nonempty {x : X // f x = y} := by
    let ⟨x, hx⟩ := hf y
    exact ⟨⟨x, hx⟩⟩
  -- 選択原理を用いて f x = y なる x : X を構成する
  have x := Classical.choice this
  exact x.val

/- 3.5.4 練習問題 -/
/-- 対偶が元の命題と同値であることを認めれば二重否定の除去が導ける -/
theorem double_negation_of_contra_equiv (P : Prop)
  (contra_equiv : ∀ (P Q : Prop), (¬P → ¬Q) ↔ (Q → P)) : ¬¬P → P := by
  apply (contra_equiv P ¬¬P).mp
  intro hnp hnnp
  exact hnnp hnp

-- Classical.choice に依存していないことを確認する
#print axioms double_negation_of_contra_equiv
