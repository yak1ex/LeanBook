/-- 自前で実装した自然数 -/
inductive MyNat where
  /-- ゼロ -/
  | zero
  /-- 後者関数(nに対してn+1を返す関数) -/
  | succ (n: MyNat)

#check MyNat.zero
#check MyNat.succ

#check MyNat.succ .zero

/-- 自前で定義した1 -/
def MyNat.one := MyNat.succ .zero

/-- 自前で定義した2 -/
def MyNat.two := MyNat.succ .one

/-- MyNat同士の足し算 -/
def MyNat.add (m n : MyNat) : MyNat :=
  match n with
  | .zero => m
  | .succ n  => succ (add m n)

#check MyNat.add .one .one = .two

-- #reduceコマンドの結果表示をカスタマイズするための設定
set_option pp.fieldNotation.generalized false

#reduce MyNat.add .one .one

#reduce MyNat.two

/-- 1+1=2のMyNatにおける証明 -/
example : MyNat.add .one .one = .two := by
  rfl

/-- 演習問題2.2.7
    ゼロを右から足しても値は変わらない -/
example (n: MyNat) : MyNat.add n .zero = n := by
  rfl
