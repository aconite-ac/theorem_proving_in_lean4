# Type Classes (型クラス)

型クラスは、関数型プログラミング言語においてアドホックな多相性を実現する原理的な方法として導入された。まず、次のことを見る: もし関数が型固有の加法の実装を引数として取り、残りの引数に対してその加法の実装を呼び出すだけであれば、加法のようなアドホックな多相性関数を実装するのは簡単である。例えば、Leanで加法の実装を保持する構造体を宣言したとしよう。

```lean
# namespace Ex
structure Add (a : Type) where
  add : a → a → a

#check @Add.add
-- Add.add : {a : Type} → Add a → a → a → a
-- `Add.add` はstructure宣言によって自動生成される射影関数
# end Ex
```

このLeanコードでは、``add`` フィールドへの射影関数は ``Add.add : {a : Type} → Add a → a → a → a`` という型を持っている。ここで、型 ``a`` を囲んでいる波括弧は、``a`` が暗黙の引数であることを示している。次のようにして ``double`` 関数を実装することができる:

```lean
# namespace Ex
# structure Add (a : Type) where
#  add : a → a → a
def double (s : Add a) (x : a) : a :=
  s.add x x

#eval double { add := Nat.add } 10
-- 20

#eval double { add := Nat.mul } 10
-- 100

#eval double { add := Int.add } 10
-- 20
# end Ex
```

``double { add := Nat.add } n`` と書くことで自然数 ``n`` を2倍することができる。もちろん、このように手動で実装(を保持するレコード)を渡すのはユーザーにとって非常に面倒である。実際、そのような面倒さがあれば、アドホック多相性の潜在的な利点のほとんどを失うことになる。

型クラスの主な考え方は、まず ``Add a`` のような型の引数を暗黙にすることである。それから、ユーザーが定義したインスタンスを保管するデータベースを使用して、*typeclass resolution*(型クラス解決)として知られるプロセスを通じて、目的のインスタンス ``{s : Add a}`` を自動合成することである。Leanでは、上の例で ``structure`` を ``class`` に書き換えることで、``Add.add`` の型は次のように変化する:

```lean
# namespace Ex
class Add (a : Type) where
  add : a → a → a

#check @Add.add
-- Add.add : {a : Type} → [self : Add a] → a → a → a
# end Ex
```

ここで、角括弧 ``[]`` は ``Add a`` 型の引数が*instance implicit*(インスタンス暗黙引数)であること、つまり型クラス解決を使って合成されるべきであることを示している。``class`` 宣言によって自動生成された ``add`` 射影関数は、Haskellの ``add :: Add a => a -> a -> a`` のLean版である。そして、ユーザー定義インスタンスは次のように登録できる:

```lean
# namespace Ex
# class Add (a : Type) where
#  add : a → a → a
instance : Add Nat where
  add := Nat.add

instance : Add Int where
  add := Int.add

instance : Add Float where
  add := Float.add
# end Ex
```

インスタンスの登録後、``n : Nat`` と ``m : Nat`` に対して、``Add.add n m`` という項は、``Add Nat`` 型のインスタンス合成を目標とする型クラス解決を引き起こす。型クラス解決は上で ``instance`` 宣言を用いて登録した ``Add Nat`` のインスタンスを参照し、目標のインスタンスを合成する。インスタンス暗黙引数を使って、``double`` を再実装することができる:

```lean
# namespace Ex
# class Add (a : Type) where
#   add : a → a → a
# instance : Add Nat where
#  add := Nat.add
# instance : Add Int where
#  add := Int.add
# instance : Add Float where
#  add := Float.add
def double [Add a] (x : a) : a :=
  Add.add x x

#check @double
-- @double : {a : Type} → [inst : Add a] → a → a

#eval double 10
-- 20

#eval double (10 : Int)
-- 20

#eval double (7 : Float)
-- 14.000000

#eval double (239.0 + 2)
-- 482.000000

# end Ex
```

<!--
(訳者注: この時点では、大雑把に言えば、型クラスは型クラス解決によりインスタンスが自動合成される構造体だといえる。)
-->

一般的に、インスタンスは複雑な方法で他のインスタンスに依存することがある。例えば、「もし ``a`` が加法を持つなら、``Array a`` も加法を持つ」と主張する(匿名)インスタンスを宣言することができる:

```lean
instance [Add a] : Add (Array a) where
  add x y := Array.zipWith x y (· + ·)

#eval Add.add #[1, 2] #[3, 4]
-- #[4, 6]

#eval #[1, 2] + #[3, 4]
-- #[4, 6]
```

Leanにおいて ``(· + ·)`` は ``fun x y => x + y`` の略記であることに注意してほしい。

上記の例では、記法をオーバーロード(多重定義)するために型クラスを使う方法を実践した。別の応用例も見てみよう。まず、Leanにおいて、型は項を1つも持たないことがあることを思い出してほしい。しかし、型が有項なら、その型について様々なことができるようになる。Leanを使っていると、ある型の任意の項が必要になることがよくある。例えば、「コーナーケース」において任意の項を返す関数を定義したいと思うことがよくある。また、``xs`` が ``List a`` 型を持つとき、``head xs`` は ``a`` 型を持ってほしいと思うかもしれない。同様に、型が空でないという付加的な仮定の下では、多くの付加的な定理が成立する。例えば、``a`` が型であるとき、``exists x : a, x = x`` が成立するためには ``a`` が空でないことが必要である。標準ライブラリは、有項型の*default*要素を推論できるようにするために、``Inhabited`` という型クラスを定義している。今述べた応用例を実践するために、まず適切なクラスを宣言することから始めよう:

```lean
# namespace Ex
class Inhabited (a : Type u) where
  default : a

#check @Inhabited.default
-- Inhabited.default : {a : Type u} → [self : Inhabited a] → a
# end Ex
```

``Inhabited.default`` は明示的な引数を持たないことに注意してほしい。

``Inhabited a`` クラスの項とは、ある項 ``x : a`` に対する ``Inhabited.mk x`` という形の式である。射影 ``Inhabited.default`` を使えば、``Inhabited a`` の項から ``a`` の項 ``x`` を「抽出」することができる。次に、このクラスにいくつかのインスタンスを登録する:

```lean
# namespace Ex
# class Inhabited (a : Type _) where
#  default : a
instance : Inhabited Bool where
  default := true

instance : Inhabited Nat where
  default := 0

instance : Inhabited Unit where
  default := ()

instance : Inhabited Prop where
  default := True

#eval (Inhabited.default : Nat)
-- 0

#eval (Inhabited.default : Bool)
-- true
# end Ex
```

``export`` コマンドを使うと、``Inhabited.default`` に対して別名 ``default`` を生成することができる(正確には、``export`` コマンドは名前空間 ``Foo`` 内で ``Bar.baz`` に対して別名 ``Foo.baz`` を生成する)。

```lean
# namespace Ex
# class Inhabited (a : Type _) where
#  default : a
# instance : Inhabited Bool where
#  default := true
# instance : Inhabited Nat where
#  default := 0
# instance : Inhabited Unit where
#  default := ()
# instance : Inhabited Prop where
#  default := True
export Inhabited (default)

#eval (default : Nat)
-- 0

#eval (default : Bool)
-- true
# end Ex
```

## Chaining Instances (インスタンスの連鎖)

型クラス推論で出来ることがこれで終わりだとしたら、それほど印象的なものではないだろう。もしそうなら、型クラス推論はユーザー定義インスタンスを保存して、elaboratorがルックアップテーブル(配列や連想配列などのデータ構造)からそれらを見つけられるようにする仕組みに過ぎないからである。型クラス推論が強力なのは、インスタンスを「連鎖」させることができるからである。つまり、インスタンス宣言は、他の型クラスの暗黙のインスタンスに依存することができる。これにより、型クラス推論は、Prolog-likeな探索を用いて、必要に応じてバックトラッキングしながら、再帰的にインスタンスを連鎖させることができる。

例えば、次の定義は、2つの型 ``a`` と ``b`` が有項なら、その直積型 ``a × b`` も有項であることを示している:

```lean
instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)
```

前節のインスタンス宣言に今の宣言を加えることで、例えば ``Nat × Bool`` のデフォルト項を推論できるようになる:

```lean
# namespace Ex
# class Inhabited (a : Type u) where
#  default : a
# instance : Inhabited Bool where
#  default := true
# instance : Inhabited Nat where
#  default := 0
# opaque default [Inhabited a] : a :=
#  Inhabited.default
instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)

#eval (default : Nat × Bool)
-- (0, true)
# end Ex
```

同様に、適切な定数関数の存在により、型 ``b`` が有項なら関数型 ``a → b`` も有項であることを示すことができる:

```lean
instance [Inhabited b] : Inhabited (a → b) where
  default := fun _ => default
```

練習として、``List`` 型や ``Sum`` 型などの他の型のデフォルトインスタンスを定義してみよう。

Leanの標準ライブラリには ``inferInstance`` という定義がある。これは型 ``{α : Sort u} → [i : α] → α`` を持ち、期待される型がインスタンスを持つときに型クラス解決手続きを実行させるのに便利である。

```lean
#check (inferInstance : Inhabited Nat) -- Inhabited Nat

def foo : Inhabited (Nat × Nat) :=
  inferInstance

#eval foo.default  -- (0, 0)

theorem ex : foo.default = (default, default) :=
  rfl
```

``#print`` コマンドを使うと、``inferInstance`` がいかにシンプルかを見ることができる。

```lean
#print inferInstance
```

## ToString (``ToString`` 型クラス)

``ToString`` 型クラスの多相メソッド ``toString`` は型 ``{α : Type u} → [ToString α] → α → String`` を持つ。ユーザー定義の型 ``Foo`` に対して型 ``ToString Foo`` のインスタンスを宣言すると、連鎖を利用して複雑な値を文字列に変換することができる。Leanでは、ほとんどのビルトイン型 ``α`` について ``ToString α`` のインスタンスが付属している。

```lean
structure Person where
  name : String
  age  : Nat

instance : ToString Person where
  toString p := p.name ++ "@" ++ toString p.age

#eval toString { name := "Leo", age := 542 : Person }
#eval toString ({ name := "Daniel", age := 18 : Person }, "hello")  -- `instToStringProd` と `instToStringPerson` の連鎖

```

## Numerals (数字)

Leanでは数字は多相である。型クラス ``OfNat`` に関するインスタンスを持つ任意の型の項を表すために、数字(例えば ``2``)を使うことができる。

```lean
structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

instance instOfNatRational (n : Nat) : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#eval (2 : Rational) -- 2/1

#check (2 : Rational) -- Rational
#check (2 : Nat)      -- Nat

#check @OfNat.ofNat Nat 2 (instOfNatNat 2)  -- Nat
#check @OfNat.ofNat Rational 2 (instOfNatRational 2)  -- Rational
```

Leanのelaboratorは、項 ``(2 : Nat)`` と ``(2 : Rational)`` をそれぞれ ``@OfNat.ofNat Nat 2 (instOfNatNat 2)`` と ``@OfNat.ofNat Rational 2 (instOfNatRational 2)`` に変換する。変換後の項中に出現する数字 ``2`` は「生の」自然数と呼ばれる。マクロ ``nat_lit 2`` を使うと生の自然数 ``2`` を入力することができる。

```lean
#check nat_lit 2  -- Nat
```

生の自然数は多相では**ない**。

``OfNat`` インスタンスは生の自然数を引数に取る。そのため、特定の数字に対して ``OfNat`` のインスタンスを定義することができる。``OfNat`` 型クラスの2番目の引数は、上の例のように変数であることが多いが、生の自然数の場合もある。

```lean
class Monoid (α : Type u) where
  unit : α
  op   : α → α → α

instance [s : Monoid α] : OfNat α (nat_lit 1) where
  ofNat := s.unit

def getUnit [Monoid α] : α :=
  1
```

## Output Parameters (出力パラメータ)

デフォルトでは、Leanは型 ``T`` のデフォルト項が既知であり、``T`` が欠落部分を含まない場合にのみ、``Inhabited T`` のインスタンスを合成しようとする。次のコマンドは、型が欠落部分(つまり ``_``)を含むため、"failed to create type class instance for Inhabited (Nat × ?m.1499)" というエラーを生成する。

```lean
#check_failure (inferInstance : Inhabited (Nat × _))
```

``Inhabited`` 型クラスのパラメータは、``Inhabited`` 型クラスのコンストラクタの「入力」の型とみなすことができる。型クラスが複数のパラメータを持つ場合、そのうちのいくつかを出力パラメータ(型クラスのインスタンス合成時に、既に与えられた型から推論される型)としてマークすることができる。出力パラメータの推論のために使われる型は入力パラメータと呼ばれる。出力パラメータに欠落部分があっても、Leanは型クラスのインスタンス合成を開始する。以下の例では、出力パラメータを使って*heterogeneous*(異種)多相乗法を定義している。

```lean
# namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Nat (Array Nat) (Array Nat) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 4 3           -- 12
#eval hMul 4 #[2, 3, 4]  -- #[8, 12, 16]
# end Ex
```

パラメータ ``α`` と ``β`` は入力パラメータ、``γ`` は出力パラメータとみなされる。関数適用 ``hMul a b`` が与えられると、``a`` と ``b`` の型が分かっているなら型クラスインスタンス合成器が呼び出され、型クラスインスタンス合成器は ``hMul a b`` の出力の型情報を(入力パラメータ ``α`` と ``β`` から推論された)出力パラメータ ``γ`` から得る。上の例では、2つのインスタンスを定義した。最初のインスタンスは自然数上の同種乗法である。2つ目のインスタンスは配列のスカラー倍である。2つ目のインスタンスの定義では、インスタンスの連鎖が使われていることに注意してほしい。

```lean
# namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Int Int Int where
  hMul := Int.mul

instance [HMul α β γ] : HMul α (Array β) (Array γ) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 4 3                    -- 12
#eval hMul 4 #[2, 3, 4]           -- #[8, 12, 16]
#eval hMul (-2) #[3, -1, 4]       -- #[-6, 2, -8]
#eval hMul 2 #[#[2, 3], #[0, 4]]  -- #[#[4, 6], #[0, 8]]
# end Ex
```

この新しい配列スカラー倍インスタンスは、``HMul α β γ`` のインスタンスがあれば、いつでも ``Array β`` 型の配列と ``α`` 型のスカラーに対して使用することができる。最後の ``#eval`` では、``HMul Nat Nat Nat`` のインスタンスから ``HMul Nat (Array Nat) (Array Nat)`` のインスタンスが合成され、``HMul Nat (Array Nat) (Array Nat)`` のインスタンスから ``HMul Nat (Array (Array Nat)) (Array (Array Nat))`` のインスタンスが合成されていることに注意してほしい。

## Default Instances (デフォルトインスタンス)

型クラス ``HMul`` では、パラメータ ``α`` と ``β`` は入力パラメータとして扱われる。したがって、型クラスインスタンス合成はこれら2つの型が特定されてから開始される。場合によっては、この制約は強すぎるかもしれない。

```lean
# namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

-- Error "typeclass instance problem is stuck, it is often due to metavariables HMul ?m.89 ?m.90 ?m.91"
-- `y` の型を明示的に与えればエラーは消える
#check_failure fun y => xs.map (fun x => hMul x y)
# end Ex
```

``y`` の型が与えられていないため、``HMul`` のインスタンスはLeanによって合成されない。しかし、このような状況では ``y`` と ``x`` の型は同じはずだと考えるのが自然である。*default instances*(デフォルトインスタンス)を使えば、まさにそれを実現できる。

```lean
namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

@[default_instance]
instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

#check fun y => xs.map (fun x => hMul x y)    -- Int → List Int
#eval (fun y => xs.map (fun x => hMul x y)) 3 -- [3, 6, 9]
end Ex
```

上記のインスタンスに ``default_instance`` 属性を付けることで、保留中の型クラスインスタンス合成問題においてこのインスタンスを使用するようLeanに指示することができる。実際のLeanの実装では、各算術演算子について同種型クラス(``Add`` など)と異種型クラス(``HAdd`` など)が定義されている。さらに言うと、``a+b``、``a*b``、``a-b``、``a/b``、``a%b`` は異種版演算子を表す。``OfNat Nat n`` のインスタンスは ``OfNat`` 型クラスのデフォルトインスタンス(優先度100)である。これが、期待される型が不明な場合に、数字 ``2`` が ``Nat`` 型を持つ理由である。より高い優先度を持つデフォルトインスタンスを定義することで、ビルトインのデフォルトインスタンスをオーバーライドすることができる。

```lean
structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

@[default_instance 200]
instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#check 2 -- Rational
```

優先度は、異なるデフォルトインスタンス間の相互作用を制御するのにも便利である。例えば、``xs`` が ``List α`` 型を持つとする。elaboratorが式 ``xs.map (fun x => 2 * x)`` を解釈するとき、この式が多相性を持つために、同種乗法のデフォルトインスタンスが ``OfNat`` のデフォルトインスタンスより高い優先度を持つようにしたい。これは、``HMul α α α`` のインスタンスを実装し、``HMul Nat α α`` のインスタンスは実装しなかった場合に特に重要である。ここで、Leanにおいて表記 ``a*b`` がどう定義されているかを種明かしする。

```lean
# namespace Ex
class OfNat (α : Type u) (n : Nat) where
  ofNat : α

@[default_instance]
instance (n : Nat) : OfNat Nat n where
  ofNat := n

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

class Mul (α : Type u) where
  mul : α → α → α

@[default_instance 10]
instance [Mul α] : HMul α α α where
  hMul a b := Mul.mul a b

infixl:70 " * " => HMul.hMul
# end Ex
```

``Mul`` 型クラスは、同種乗法は実装されているが異種乗法は実装されていない型を扱う際に便利である。

## Local Instances (ローカルインスタンス)

Leanにおいて、型クラスのインスタンスは属性を用いて実装される。そのため、``local`` 修飾子を使うことで、そのインスタンスが現在のセクションや名前空間が閉じられるまで、あるいは現在のファイルの終わりまでしか効果がないことを示すことができる。

```lean
structure Point where
  x : Nat
  y : Nat

section

local instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end -- もうインスタンス `Add Point` は使えない

-- def triple (p : Point) :=
--  p + p + p  -- Error: failed to synthesize instance
```

コマンド ``attribute [-instance]`` を使えば、現在のセクションや名前空間が閉じられるまで、あるいは現在のファイルの終わりまで、指定したインスタンスを一時的に無効化することもできる。

```lean
structure Point where
  x : Nat
  y : Nat

instance addPoint : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

attribute [-instance] addPoint

-- def triple (p : Point) :=
--  p + p + p  -- Error: failed to synthesize instance
```

コマンド ``attribute [-instance]`` は問題の分析時にのみ使うことを勧める。

## Scoped Instances (スコープ付きインスタンス)

``scoped instance`` を用いてスコープ付きのインスタンスを宣言することもできる。スコープ付きインスタンスは、名前空間の中にいるとき、または名前空間を開いているときのみ使用可能である。

```lean
structure Point where
  x : Nat
  y : Nat

namespace Point

scoped instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end Point
-- インスタンス `Add Point` はもう使えない

-- #check fun (p : Point) => p + p + p  -- Error

namespace Point
-- インスタンス `Add Point` は再び利用可能になった
#check fun (p : Point) => p + p + p

end Point

open Point -- 名前空間を開き、インスタンス `Add Point` を利用可能にする
#check fun (p : Point) => p + p + p
```

コマンド ``open scoped <namespace>`` を使うと、名前空間 ``<namespace>`` 内の ``scoped`` 属性のついた定義が利用可能になるが、名前空間 ``<namespace>`` 内のそれ以外の定義に短い別名でアクセスすることはできない。

```lean
structure Point where
  x : Nat
  y : Nat

namespace Point

scoped instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end Point

open scoped Point -- インスタンス `Add Point` を利用可能にする
#check fun (p : Point) => p + p + p

-- #check fun (p : Point) => double p -- Error: unknown identifier 'double'
```

## Decidable Propositions (決定可能命題)

標準ライブラリで定義されている、命題に関する型クラス ``Decidable`` について考えてみよう。大雑把に言えば、``Prop`` 型の項(具体的な命題)は、それが真か偽かを決めることができる場合、決定可能であると言われる。古典論理において全ての命題は決定可能であるため、命題が決定可能かどうかという区別は構成的論理においてのみ有用である。古典論理を使っているかどうかの区別は重要である。古典論理を使って、例えば場合分けによって関数を定義すると、その関数は計算不能になる。

```lean
variable (p : Nat → Prop)

-- error : failed to synthesize instance
--   Decidable (p n)
/-
def bad_foo : Nat → Bool :=
  fun (n : Nat) =>
  if p n then true
  else false
-/

open Classical

noncomputable def foo : Nat → Bool :=
  fun (n : Nat) =>
  if p n then true
  else false

#print axioms foo
-- 'foo' depends on axioms: [Classical.choice, Quot.sound, propext]
```

アルゴリズム的に言えば、``Decidable`` 型クラスは、その命題が真か偽かを効果的に決定する手続きを推論するために使うことができる。結果として、この型クラスはある定義が計算可能なときその定義をサポートすると同時に、古典論理を使った定義や推論の使用へのスムーズな移行を可能にする。

標準ライブラリでは、``Decidable`` は次のように形式的に定義されている:

```lean
# namespace Hidden
class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)  : Decidable p
# end Hidden
```

論理的に言えば、項 ``t : Decidable p`` を持つことは、証明項 ``t : p ∨ ¬p`` を持つことよりも強い。項 ``t : Decidable p`` の存在は、``p`` の真理値に依存して任意の型の値や関数を定義することを可能にする。例えば、``if p then a else b`` という式が意味をなすには、``p`` が決定可能であることを知っている必要がある。ここで ``if p then a else b`` は ``ite p a b`` の糖衣構文である。``ite`` は次のように定義される:

```lean
# namespace Hidden
def ite {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α :=
  Decidable.casesOn (motive := fun _ => α) h (fun _ => e) (fun _ => t)
# end Hidden
```

標準ライブラリは ``dite`` と呼ばれる ``ite`` の変形版を持っている。``dite`` は依存版if-then-else式である。これは次のように定義される:

```lean
# namespace Hidden
def dite {α : Sort u} (c : Prop) [h : Decidable c] (t : c → α) (e : Not c → α) : α :=
  Decidable.casesOn (motive := fun _ => α) h e t
# end Hidden
```

つまり、``dite c t e`` において、「then」分岐では ``hc : c`` を、「else」分岐では ``hnc : ¬ c`` を仮定できる。Leanでは、``dite`` をより使いやすくするために、``dite c (λ h : c => t) (λ h : ¬ c => e)`` の代わりに ``if h : c then t else e`` と書くことができる。

古典論理がなければ、全ての命題が決定可能であることを証明することはできない。しかし、**ある**命題が決定可能であることは証明できる。例えば、自然数や整数に関する等式や不等式のような基本関係の決定可能性は古典論理なしで証明できる。さらに、決定可能性は命題結合子の適用前後で保存される:

```lean
#check @instDecidableAnd
  -- {p q : Prop} → [Decidable p] → [Decidable q] → Decidable (And p q)

#check @instDecidableOr
#check @instDecidableNot
```

したがって、自然数上の決定可能述語を用いた場合分けによって関数を定義することができる:

```lean
def step (a b x : Nat) : Nat :=
  if x < a ∨ x > b then 0 else 1

set_option pp.explicit true  -- 暗黙の引数を表示する
#print step
```

暗黙の引数の表示をオンにすると、elaboratorは適切なインスタンス ``instDecidableOr`` と ``Nat.decLt`` を適用しただけで、命題 ``x < a ∨ x > b`` の決定可能性を推論したことがわかる。

古典論理の公理を使うと、全ての命題が決定可能であることが証明できる。``Classical`` 名前空間を開くと、古典論理の公理がインポートされ、全ての命題 ``p`` に対して ``Decidable p`` のインスタンスが利用できるようになる。

```lean
open Classical
```

したがって、古典論理的に推論したい場合、決定可能性を前提とするライブラリ内の定理は、全て自由に利用できる。[12章 Axioms and Computation (公理と計算)](./axioms_and_computation.md)では、排中律を使って関数を定義すると、その関数が計算に使われなくなることがあることを説明する。したがって、標準ライブラリでは ``Classical.propDecidable`` インスタンスに低い優先度を割り当てている。

```lean
# namespace Hidden
open Classical
noncomputable scoped
instance (priority := low) propDecidable (a : Prop) : Decidable a :=
  choice <| match em a with
    | Or.inl h => ⟨isTrue h⟩
    | Or.inr h => ⟨isFalse h⟩
# end Hidden
```

これは、``Decidable p`` の型クラス解決において、Leanが他のインスタンスを優先し、他の試みが全て失敗した後にのみインスタンス ``propDecidable p`` を使うことを保証する。

``Decidable`` 型クラスは、定理証明の小規模な自動化もいくつか提供している。標準ライブラリには、``Decidable`` のインスタンスを使って単純なゴールを解くタクティク ``decide`` が含まれている。

```lean
example : 10 < 5 ∨ 1 > 0 := by
  decide

example : ¬ (True ∧ False) := by
  decide

example : 10 * 20 = 200 := by
  decide

theorem ex : True ∧ 2 = 1+1 := by
  decide

#print ex
-- theorem ex : True ∧ 2 = 1 + 1 :=
-- of_decide_eq_true (Eq.refl true)

#check @of_decide_eq_true
-- ∀ {p : Prop} [Decidable p], decide p = true → p

#check @decide
-- (p : Prop) → [Decidable p] → Bool
```

これらは次のように動作する。式 ``decide p`` は ``p`` の決定可能性を用いて ``p`` の真偽決定手続きの推論を試み、成功すれば ``decide p`` は ``true`` か ``false`` のどちらかに評価される。特に、``p`` が正しい閉論理式である場合、``decide p`` はdefinitionallyにブール値 ``true`` に簡約される。``decide p = true`` が成立するという前提を受け取ると、``of_decide_eq_true`` は ``p`` の証明を出力する。ターゲット ``p`` を証明するために以上の過程をまとめたものが ``decide`` タクティクである。前述した内容により、``decide`` は、推論された ``c`` の真偽決定手続きが、``c`` が ``isTrue`` の場合であることをdefinitionallyに評価するために十分な情報を持っていれば、いつでも成功する。

## Managing Type Class Inference (型クラス推論の管理)

Leanの型クラス推論によって合成できる式 ``t`` を提供する必要があるとき、``inferInstance`` を使うと ``t`` を推論によって合成するようLeanに依頼することができる:

```lean
def foo : Add Nat := inferInstance
def bar : Inhabited (Nat → Nat) := inferInstance

#check @inferInstance
-- {α : Sort u} → [α] → α
```

Leanの ``(t : T)`` 記法を使えば、今探している ``t`` がどの型クラス ``T`` のインスタンスなのかを簡潔に指定することができる:

```lean
#check (inferInstance : Add Nat)
```

型 ``T`` を引数に取る補助定義 ``inferInstanceAs`` を使うこともできる:

```lean
#check inferInstanceAs (Add Nat)

#check @inferInstanceAs
-- (α : Sort u) → [α] → α
```

型クラスが定義の下に埋もれているために、Leanがインスタンスを見つけられないことがある。例えば、単に ``inferInstance`` を使うだけで ``Inhabited (Set α)`` のインスタンスを見つけることはできない。この場合、定義を使って ``Set α`` を ``α → Prop`` に書き下し、それを明示的に与えればよい:

```lean
def Set (α : Type u) := α → Prop

-- fails
-- example : Inhabited (Set α) :=
--  inferInstance

instance : Inhabited (Set α) :=
  inferInstanceAs (Inhabited (α → Prop))

-- 別解
example : Inhabited (Set α) :=
  @inferInstance (Inhabited (α → Prop)) _
```

時には、型クラス推論が期待されるインスタンスを見つけることに失敗したり、最悪の場合、無限ループに陥ってタイムアウトすることがある。このような状況でのデバッグを手伝ってもらうために、Leanにインスタンス探索の追跡を依頼することができる:

```lean
set_option trace.Meta.synthInstance true
```

VSCodeを使用している場合は、関連する定理や定義にカーソルを合わせるか、``Ctrl-Shift-Enter`` によりメッセージウィンドウを開くことで、追跡結果を読むことができる。Emacsでは、``C-c C-x`` によりファイルと独立したLeanプロセスを実行することができる。その後、出力バッファには型クラス解決手順が起きるたびに追跡内容が表示される。

次のオプションを使ってインスタンス探索を制限することもできる:

```lean
set_option synthInstance.maxHeartbeats 10000
set_option synthInstance.maxSize 400
```

``synthInstance.maxHeartbeats`` オプションは、型クラス解決問題ごとのheartbeatsの最大量を指定する。heartbeatsとは(小さな)メモリ割り当ての数(1000単位)であり、``synthInstance.maxHeartbeats 0`` は制限がないことを意味する。``synthInstance.maxSize`` オプションは、型クラスインスタンス合成過程で解を構築するために使われるインスタンスの最大数を指定する。

VSCodeでもEmacsでも、``set_option`` の中でタブ補完が機能することを覚えてほしい。タブ補完は適切なオプションを探すのに役立つ。

上述したように、与えられたコンテキストでの型クラスインスタンス合成はProlog-likeなプログラムであり、これはバックトラック探索を生じさせる。プログラムの効率も発見される解も、システムがインスタンスを探索する順番に依存して変化する。探索においては、最後に宣言されたインスタンスから順番に探索される。さらに、インスタンスが他のモジュール(ファイル)で宣言されている場合、インスタンスが探索される順番は名前空間を開いた順番に依存する。後に開いた名前空間で宣言されたインスタンスほど先に探索される。

型クラスのインスタンスに「優先度」を割り当てることで、探索される順番を変更することができる。普通にインスタンスが宣言されると、そのインスタンスにはデフォルトの優先度が割り当てられる。インスタンスを定義するとき、デフォルト以外の優先度を割り当てることができる。次の例はその方法を示している:

```lean
class Foo where
  a : Nat
  b : Nat

instance (priority := default+1) i1 : Foo where
  a := 1
  b := 1

instance i2 : Foo where
  a := 2
  b := 2

example : Foo.a = 1 :=
  rfl

instance (priority := default+2) i3 : Foo where
  a := 3
  b := 3

example : Foo.a = 3 :=
  rfl
```

## Coercions using Type Classes (型クラスを用いた強制)

最も基本的なタイプの(型)強制は、ある型の項を別の型の項にマッピングする。例えば、``Nat`` 型から ``Int`` 型への強制は、任意の項 ``n : Nat`` を ``Int`` の項とみなすことを可能にする。しかし、いくつかの強制はより複雑で、パラメータに依存する。例えば、任意の型 ``α`` に対して、任意の項 ``as : List α`` を ``Set α`` の項、つまりリストに出現する ``α`` の項全体からなる集合とみなすことが可能である。これに対応する強制は、``α`` によってパラメータ化された型の「族」``List α`` 上で定義される。

Leanでは3種類の強制を宣言することができる:

- ある型の族から他の型の族への強制
- ある型の族からSortのクラスへの強制
- ある型の族から関数型のクラスへの強制

1種類目の強制は、強制元の族に属する型の任意の「項」を、強制先の族に属する対応する型の「項」として見ることを可能にする。2種類目の強制は、強制元の族に属する型の任意の「項」を「型」として見ることを可能にする。3種類目の強制は、強制元の族に属する型の任意の「項」を「関数」として見ることを可能にする。それぞれを順番に考えてみよう:

```lean
instance : Coe Bool Prop where
  coe b := b = true
```

この強制により、if-then-else式の条件の中でブール型の項を使うことができる:

```lean
#eval if true then 5 else 3
#eval if false then 5 else 3
```

``List α`` から ``Set α`` への強制は次のように定義される:

```lean
# def Set (α : Type u) := α → Prop
# def Set.empty {α : Type u} : Set α := fun _ => False
# def Set.mem (a : α) (s : Set α) : Prop := s a
# def Set.singleton (a : α) : Set α := fun x => x = a
# def Set.union (a b : Set α) : Set α := fun x => a x ∨ b x
# notation "{ " a " }" => Set.singleton a
# infix:55 " ∪ " => Set.union
def List.toSet : List α → Set α
  | []    => Set.empty
  | a::as => {a} ∪ as.toSet

instance : Coe (List α) (Set α) where
  coe a := a.toSet

def s : Set Nat := {1}
#check s ∪ [2, 3]
-- s ∪ List.toSet [2, 3] : Set Nat
```

特定の場所に明示的に強制を導入するために、``↑`` という記法を使うことができる。この記法は書き手の意図を明確にすることや、強制解決システムの制限を回避することにも役立つ。

```lean
# def Set (α : Type u) := α → Prop
# def Set.empty {α : Type u} : Set α := fun _ => False
# def Set.mem (a : α) (s : Set α) : Prop := s a
# def Set.singleton (a : α) : Set α := fun x => x = a
# def Set.union (a b : Set α) : Set α := fun x => a x ∨ b x
# notation "{ " a " }" => Set.singleton a
# infix:55 " ∪ " => Set.union
# def List.toSet : List α → Set α
#   | []    => Set.empty
#   | a::as => {a} ∪ as.toSet
# instance : Coe (List α) (Set α) where
#   coe a := a.toSet
def s : Set Nat := {1}

#check let x := ↑[2, 3]; s ∪ x
-- let x := List.toSet [2, 3]; s ∪ x : Set Nat
#check let x := [2, 3]; s ∪ x
-- let x := [2, 3]; s ∪ List.toSet x : Set Nat
```

Leanは ``CoeDep`` 型クラスを使った依存強制もサポートしている。例えば、``Prop`` 型の任意の項 ``p`` をBool型の項に強制することはできないが、``Decidable p`` 型クラスがインスタンスを持つような ``p`` だけはBool型の項に強制できる。

```lean
instance (p : Prop) [Decidable p] : CoeDep Prop p Bool where
  coe := decide p
```

Leanは必要に応じて(非依存)強制を連鎖させる。実際、型クラス ``CoeT`` は ``Coe`` の推移的閉包である。

次に、2種類目の強制について考えよう。「Sortのクラス」とは、宇宙 ``Type u`` の集まりを意味する。2種類目の強制は次のような形をとる:

```
    c : (x1 : A1) → ... → (xn : An) → F x1 ... xn → Type u
```

ここで、``F`` は型の族であり、``F x1 ... xn`` は型の族に属する特定の型である。この種類の強制により、``t`` が型 ``F a1 ... an`` の項であるときは、いつでも ``s : t`` と書くことができる。言い換えれば、この強制は ``F a1 ... an`` の項を型として見ることを可能にする。これは、構造体の1つの要素、つまり構造の台(集合) ``carrier`` が型であるような代数的構造を定義するときに非常に便利である。例えば、*semigroup*(半群)は次のように定義できる:

```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)

instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b
```

つまり、半群は型 ``carrier``、乗法 ``mul``、「乗法は結合的である」という性質の3要素からなる。上記の ``instance`` コマンドは、``a b : S.carrier`` があるとき、``Semigroup.mul S a b`` を ``a * b`` と略記することを可能にする。Leanは ``a`` と ``b`` の型からインスタンスの引数 ``S`` を推測できることに注意してほしい。関数 ``Semigroup.carrier`` はクラス ``Semigroup`` の項(半群)を ``Type u`` の項(型)にマッピングする:

```lean
# structure Semigroup where
#   carrier : Type u
#   mul : carrier → carrier → carrier
#   mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
# instance (S : Semigroup) : Mul S.carrier where
#   mul a b := S.mul a b
#check Semigroup.carrier
```

この関数は強制であると宣言すれば、半群 ``S : Semigroup`` があるときはいつでも、``a : S.carrier`` を ``a : S`` と略記することができる:

```lean
# structure Semigroup where
#   carrier : Type u
#   mul : carrier → carrier → carrier
#   mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
# instance (S : Semigroup) : Mul S.carrier where
#   mul a b := S.mul a b
instance : CoeSort Semigroup (Type u) where
  coe s := s.carrier

example (S : Semigroup) (a b c : S) : (a * b) * c = a * (b * c) :=
  Semigroup.mul_assoc _ a b c
```

上記の ``CoeSort Semigroup (Type u)`` のインスタンスは、``(a b c : S)`` と書くことを可能にする強制である。ここで、2種類目の強制では ``Coe Semigroup (Type u)`` ではなく ``CoeSort Semigroup (Type u)`` のインスタンスを定義したことに注意してほしい。

最後に、3種類目の強制について考えよう。「関数型のクラス」とは、依存関数型(パイ型) ``(z : B) → C`` の集まりを意味する。3種類目の強制は次のような形をとる:

```
    c : (x1 : A1) → ... → (xn : An) → (y : F x1 ... xn) → (z : B) → C
```

ここで、``F`` は再び型の族であり、``F x1 ... xn`` は型の族に属する特定の型である。``B`` と ``C`` は ``x1, ..., xn, y`` に依存することができる。この種類の強制により、``t`` が ``F a1 ... an`` の項であるときは、いつでも ``t s`` と書くことができる。言い換えれば、この強制は ``F a1 ... an`` の項を関数として見ることを可能にする。上記の例の続きとして、半群 ``S1`` と ``S2`` の間の*morphism*(射)あるいは*homomorphism*(準同型)という概念を定義できる。射とは、``S1`` の台から ``S2`` の台への、乗法を保存する(``mor (a * b) = (mor a) * (mor b)``)関数である。次のコードでは、``S1``、``S2``、``*`` に関する暗黙の強制に注意してほしい。射影 ``Morphism.mor`` は、構造体 ``Morphism S1 S2`` の項を受け取り、射の台関数を返す:

```lean
# structure Semigroup where
#   carrier : Type u
#   mul : carrier → carrier → carrier
#   mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
# instance (S : Semigroup) : Mul S.carrier where
#   mul a b := S.mul a b
# instance : CoeSort Semigroup (Type u) where
#   coe s := s.carrier
structure Morphism (S1 S2 : Semigroup) where
  mor : S1 → S2
  resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b)

#check @Morphism.mor
```

以下のコードにより、半群間の射は3種類目の強制 ``CoeFun`` の代表例となった。

```lean
# structure Semigroup where
#   carrier : Type u
#   mul : carrier → carrier → carrier
#   mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
# instance (S : Semigroup) : Mul S.carrier where
#   mul a b := S.mul a b
# instance : CoeSort Semigroup (Type u) where
#   coe s := s.carrier
# structure Morphism (S1 S2 : Semigroup) where
#   mor : S1 → S2
#   resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b)
instance (S1 S2 : Semigroup) : CoeFun (Morphism S1 S2) (fun _ => S1 → S2) where
  coe m := m.mor

theorem resp_mul {S1 S2 : Semigroup} (f : Morphism S1 S2) (a b : S1)
        : f (a * b) = f a * f b :=
  f.resp_mul a b

example (S1 S2 : Semigroup) (f : Morphism S1 S2) (a : S1) :
      f (a * a * a) = f a * f a * f a :=
  calc f (a * a * a)
    _ = f (a * a) * f a := by rw [resp_mul f]
    _ = f a * f a * f a := by rw [resp_mul f]
```

この強制を使えば、``f.mor (a * a * a)`` を ``f (a * a * a)`` と略記することができる。関数型が期待される場所で ``Morphism`` や ``f`` が使われると、Leanは強制を挿入する。フィールド ``F`` は強制先の関数型を指定するために使われる。``F`` の型は強制元の型に依存しうる。

まとめると、1種類目の強制のために型クラス ``Coe`` があり、2種類目の強制のために型クラス ``CoeSort`` があり、3種類目の強制のために型クラス ``CoeFun`` がある。
