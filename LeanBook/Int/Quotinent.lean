/- 7.2 商とQuotient -/

/- 7.2.1 Quotient：同値類を取る操作 -/
section
  variable {α : Type} (sr : Setoid α)
  #check (Quotient.mk sr : α → Quotient sr)
end

/- 7.2.2 Quotient.inductionOn：同値類の代表元を取る -/
section
  variable {α : Type} (sr : Setoid α)
  example (a : Quotient sr) : True := by
    induction a using Quotient.inductionOn with
    | h x =>
      -- x : α が得られる
      guard_hyp x : α
      trivial
end

/- 7.2.3 Quotient.lift：関数を商へ持ち上げる操作 -/
section
  /- ## 商への関数を作る -/
  variable {α β : Type} (sr : Setoid α)
  variable (f : β → α)
  -- 自然な写像 α → Quotient sr と f を合成することで、商への関数が得られる
  #check (Quotient.mk sr ∘ f : β → Quotient sr)
end

section
  /- ## 商からの関数を作る -/
  variable {α β : Type} (sr : Setoid α)
  variable (f : α → β) (h : ∀ x y, x ≈ y → f x = f y)
  #check (Quotient.lift f h : Quotient sr → β)
end

/- 7.2.4 Quotient.sound：同値なら商へ送って等しい -/
section
  variable {α : Type} (sr : Setoid α)
  variable (x y : α) (h : x ≈ y)
  example : Quotient.mk sr x = Quotient.mk sr y := by
    apply Quotient.sound
    exact h
end

/- 7.2.5 Quotient.exact：商に送って等しいなら同値 -/
section
  /- ## 商に送って等しいなら同値 -/
  variable {α : Type} (sr : Setoid α)
  variable (x y : α)
  example (h : Quotient.mk sr x = Quotient.mk sr y) : x ≈ y := by
    apply Quotient.exact h
end

/- 7.2.6 練習問題 -/
/-- β 上の二項関係 r : β → β → Prop と関数 f : α → β があるとき
    α 上の二項関係を fun x y => r (f x) (f y) で定義できる -/
private def Rel.comap {α β : Type} (f : α → β) (r : β → β → Prop)
  : α → α → Prop :=
  fun x y => r (f x) (f y)

/-- β 上の同値関係 sr : Setoid β と関数 f : α → β があるとき
    Rel.comap f (· = ·) も同値関係になる -/
private def Setoid.comap {α β : Type} (f : α → β) (sr : Setoid β)
  : Setoid α where
  r := Rel.comap f sr.r
  iseqv := by
    constructor <;> unfold Rel.comap
    -- 反射律
    case refl =>
      intro x
      apply sr.iseqv.refl /- apply refl で通る。以下も同じ。 -/
    -- 対称律
    case symm =>
      intro x y h
      apply sr.iseqv.symm h
    -- 推移律
    case trans =>
      intro x y z hxy hyz
      apply sr.iseqv.trans hxy hyz
