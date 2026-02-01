import LeanBook.IntMathlib.OrderedAddCommGroup

/- 8.8 整数の順序関係は決定可能 -/

/- 8.8.1 0 ≤ n は決定可能 -/

/-- 商は引き算を意味する -/
theorem MyInt.mk_def (x y : MyNat) : ⟦(x, y)⟧ = (x : MyInt) - (y : MyInt) := by
  simp [ofMyNat]

def PreInt.bpos (n : PreInt) : Bool :=
  match n with
  | (n1, n2) => decide (n2 ≤ n1)

/-- 整数 n に対して 0 ≤ n かどうかを判定する関数 -/
def MyInt.bpos : MyInt → Bool := Quotient.lift PreInt.bpos <| by
  intro (a, b) (c, d) hr
  notation_simp at hr
  dsimp [PreInt.bpos]

  suffices b ≤ a ↔ d ≤ c from by
    simp_all

  constructor <;> intro h
  case mp =>
    have : a + d ≤ a +c := calc
      _ = b + c := by rw[hr]
      _ ≤ a + c := by compatible
    simp at this
    assumption
  case mpr =>
    have : b + c ≤ a + c := calc
      _ = a + d := by rw[hr]
      _ ≤ a + c := by compatible
    simp at this
    assumption

-- 後で使うので補題として用意しておく
@[simp]
theorem MyInt.bpos_def (m n : MyNat) : MyInt.bpos ⟦(m, n)⟧ = true ↔ n ≤ m := by
  dsimp [MyInt.bpos, PreInt.bpos]
  simp

/- 正当性の証明 -/

/-- 型キャストは順序と整合性がある -/
@[norm_cast]
theorem MyInt.ofMyNat_le (m n : MyNat) : (m : MyInt) ≤ (n : MyInt) ↔ m ≤ n := by
  rw [MyNat.le_iff_add]
  notation_simp
  constructor <;> intro ⟨k, hk⟩
  case mp =>
    use k
    have : ↑ (m + k) = (n : MyInt) := by
      norm_cast at hk
    norm_cast at *
  case mpr =>
    use k
    rw [← hk]
    norm_cast

theorem MyInt.le_sub_iff (x y z : MyInt)  : z ≤ x - y ↔ z + y ≤ x := by
  notation_simp
  constructor <;> intro ⟨k, hk⟩
  case mp =>
    use k
    have : z + y + ↑ k = x := calc
      _ = z + ↑ k + y := by ac_rfl
      _ = (x - y) + y  := by simp[hk]
      _ = x := by abel
    assumption
  case mpr =>
    use k
    have : z + ↑ k = x - y := calc
      _ = (z + y + ↑ k) - y := by abel
      _ = x - y := by rw[hk]
    assumption

theorem MyInt.sub_nonneg (m n : MyInt) : 0 ≤ m - n ↔ n ≤ m := by
  have := MyInt.le_sub_iff m n 0
  simp_all

theorem MyInt.bpos_iff (z : MyInt) : MyInt.bpos z = true ↔ 0 ≤ z := by
  induction z using Quotient.inductionOn with
  | h a =>
    -- z = [(x, y)] として代表元 (x, y) を取る
    obtain ⟨x, y⟩ := a
    -- そうすると示すべきことは y ≤ x ↔ 0 ≤ ↑ y ≤ ↑ x に帰着されるが
    rw [MyInt.bpos_def, MyInt.mk_def]
    rw [MyInt.sub_nonneg]
    -- これは型キャストの性質から従う
    norm_cast

  /- 決定可能性の証明 -/
  instance : DecidablePred (0 ≤ · : MyInt → Prop) := by
    intro n
    apply decidable_of_iff (MyInt.bpos n = true)
    exact MyInt.bpos_iff n

example : 0 ≤ (3 : MyInt) := by
  decide

/- 8.8.2 n ≤ m は決定可能 -/

instance : DecidableLE MyInt := by
  intro n m
  apply decidable_of_iff (0 ≤ m - n)
  exact MyInt.sub_nonneg m n

#eval (3: MyInt) ≤ 4

example : (3 : MyInt) ≤ 4 := by
  decide

instance : DecidableLT MyInt := by
  intro n m
  dsimp [(· < ·), MyInt.lt]
  infer_instance

#eval (3 : MyInt) < 4

example : (3 : MyInt) < 4 := by
  decide
