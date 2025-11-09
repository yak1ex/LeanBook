import LeanBook.FirstProof.NaturalNumber

/- 4.1 型クラスで見やすく綺麗に -/

/- 4.1.1 数散リテラルを使用できるようにする -/

/-- Nat の項から対応する MyNat の項を得る
    ただし `Nat` は Lean組み込みの自然数の型 -/
def MyNat.ofNat (n : Nat) : MyNat :=
  match n with
  | 0     => MyNat.zero
  | n + 1 => MyNat.succ (MyNat.ofNat n)

/-- OfNat のインスタンスを実装する -/
@[default_instance]
instance (n : Nat) : OfNat MyNat n where
  ofNat := MyNat.ofNat n

-- MyNat の項を数値リテラルで表せるようになった
#check 0
#check 1

/- 4.1.2 「＋」演算子を利用できるようにする -/

/-- MyNat.add を足し算として登録する -/
instance : Add MyNat where
  add := MyNat.add

-- + 演算子が使えるようになった
#check 1 + 1
#check MyNat.zero + MyNat.one

#eval  0 + 0
#eval  1 + 2

/- 4.1.3 計算結果を表示する -/

/-- MyNat 型の項を Lean 組み込みの Nat の項に変換する
    注意：返り値の方は Lean 標準の Nat -/
def MyNat.toNat (n: MyNat) : Nat :=
  match n with
  | 0     => 0
  | n + 1 => MyNat.toNat n + 1

instance : Repr MyNat where
  reprPrec n _ := repr n.toNat

#eval 0 + 0 -- 0
#eval 1 + 1 -- 2

/- 4.1.4 型クラスとは何か -/

/- 4.1.5 練習問題 -/
example (n: MyNat) : n + 0 = n := by
  sorry
