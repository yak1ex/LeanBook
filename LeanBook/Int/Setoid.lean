/- 7.1 同値関係 -/

/- 7.1.1 Leanの構造体 -/
/-- 二次元平面 -/
structure Point where
  x : Int
  y : Int

#check { x := 1, y := 2 : Point }
#check { y := 1, x := 2 : Point }

#check Point.mk -- Print.mk (x y : Int) : Point

#check Point.mk 1 2 -- { x := 1, y := 2 } : Point

#check Point.x -- Point.x (self : Point) : Int
#check Point.y -- Point.y (self : Point) : Int

#eval
  let p : Point := { x := 1, y := 2 }
  p.x

/- 7.2 Equivalence -/
/-- 同値関係 -/
/-
structure Equivalence {α : Sort u} (r : α → α → Prop) : Prop where
  /-- r は反射的： x ~ x -/
  refl : ∀ x, r x x
  /-- r は対称的： x ~ y → y ~ x -/
  symm : ∀ (x y), r a b → r b a
  /-- r は推移的： x ~ y → y ~ z → x ~ z -/
  trans : ∀ (x y z), r x y → r y z → r x z
-/

example {α : Type} (r : α → α → Prop) (h : Equivalence r) : ∀ x, r x x := by
  exact h.refl

example (α : Type) : Equivalence (fun x y : α => x = y) := by
  constructor
  -- まず反射律を示す
  case refl =>
    intro x
    rfl
  -- 次に対称律を示す
  case symm =>
    intro x y h
    rw [h]
  -- 最後に推移律を示す
  case trans =>
    intro x y z hxy hyz
    rw [hxy, hyz]

/- 7.3 Setoid -/
/-
class Setoid (α : Sort u) where
  /-- 二項関係 r : α → α → Prop -/
  r : α → α → Prop
  /-- 二項関係 r は同値関係である -/
  iseqv : Equivalence r
-/

example {α : Type} (sr : Setoid α) (x y : α) : sr.r x y = (x ≈ y) := by
  rfl

/- 7.1.4 練習問題 -/
/-- 任意の要素に対して成り立つような二項関係は同値関係である -/
example {α : Type} : Equivalence (fun _x _y : α => True) := by
  constructor <;> simp
