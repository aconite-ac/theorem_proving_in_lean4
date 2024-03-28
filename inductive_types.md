# Inductive Types (帰納型)

Leanの形式的基礎は ``Prop, Type 0, Type 1, Type 2, ...`` という基本的な型を含み、``(x : α) → β`` といった依存関数型の形成を可能にすることが分かった。例の中では、``Bool``、``Nat``、``Int`` などの追加的な型や、``List``、直積型 ``×`` などの型コンストラクタも使用した。実際、Leanのライブラリにおいて、宇宙以外の全ての具体的な型と、依存関数型以外の全ての型コンストラクタは、*inductive types*(帰納型)と呼ばれる型コンストラクタの集まりである(逆に、宇宙と依存関数型は*foundational types*(基礎型)として知られる)。型宇宙、依存関数型、そして帰納型のみで巨大で頑丈な数学の体系を構築できることは驚くべきことである。それ以外の全てはこの3種類の型から派生する。

直感的には、帰納型は指定されたコンストラクタのリストから構築される。Leanにおいて、帰納型を指定する構文は次の通りである:

```
inductive Foo where
  | constructor₁ : ... → Foo
  | constructor₂ : ... → Foo
  ...
  | constructorₙ : ... → Foo
```

直感的には、各コンストラクタは、以前に構築された項から ``Foo`` の新しい項を構築する方法を指定する。``Foo`` 型は各コンストラクタによって構築された項全てからなり、それ以外は何も含まない。帰納的宣言の最初の文字 ``|`` は省略可能である。``|`` の代わりにコンマ ``,`` を使ってコンストラクタを区切ることもできる。

以下では、コンストラクタの引数に ``Foo`` 型の項を含めることができるが、その際に ``Foo`` の任意の要素がボトムアップで構築されることを保証する、ある「正の」制約が適用されることを説明する。大雑把に言えば、各コンストラクタの引数は ``Foo`` 型と以前に定義された型からなる任意の依存関数型を持つことができる。その依存関数型の中で、``Foo`` は、もし現れるとすれば、「ターゲット」としてのみ現れる。

以下に帰納型の例をいくつか提供する。また、上記のスキームを少し一般化して、相互に定義された帰納型や、いわゆる*inductive families*(帰納族)についても考える。

論理的結合子と同様、全ての帰納型には導入則と除去則がある。導入則はその型の項の構築方法を示す。除去則は、その型の項を別の項の構築のために「使う」方法を示す。論理的結合子と帰納型の類似性は驚くにはあたらない。なぜなら、後述するように、論理的結合子たちも帰納的な型構築の例だからである。帰納型の導入則とは、すでに見た通りで型の定義で指定されるコンストラクタにすぎない。除去則はその型における再帰の原理を規定するものである。帰納法の原理は再帰の原理の特別な場合である。

次の章では、Leanの関数定義パッケージについて説明する。このパッケージは帰納型上の関数を定義し、帰納的証明を実行するためのさらに便利な方法を提供する。しかし、帰納型の概念は非常に基礎的で重要なため、低レベルで実践的な理解から始めることが重要だと考えている。ここでは、帰納型の基本的な例から始め、より精巧で複雑な例へとステップアップしていく。

## Enumerated Types (列挙型)

最も単純な帰納型は、列挙型、すなわち有限個の項を列挙したリストを持つ型である。

```lean
inductive Weekday where
  | sunday : Weekday
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
  | saturday : Weekday
```

``inductive`` コマンドは新しい型 ``Weekday`` を作成する。全てのコンストラクタは ``Weekday`` 名前空間の中に格納される。

```lean
# inductive Weekday where
#  | sunday : Weekday
#  | monday : Weekday
#  | tuesday : Weekday
#  | wednesday : Weekday
#  | thursday : Weekday
#  | friday : Weekday
#  | saturday : Weekday
#check Weekday.sunday
#check Weekday.monday

open Weekday

#check sunday
#check monday
```

帰納型 ``Weekday`` を宣言する際は、``: Weekday`` を省略できる。

```lean
inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
```

``sunday``、``monday``、...、``saturday`` は ``Weekday`` の互いに異なる項であり、それ以外に互いに異なる項はないと考えてほしい。除去則 ``Weekday.rec`` は 型 ``Weekday`` とそのコンストラクタを用いて定義されている。除去則は*recursor*(再帰子)とも呼ばれ、この型を*inductive*(帰納的)にしている: 除去則は、各コンストラクタに対応する値を割り当てることで、``Weekday`` 上の関数を定義することを可能にしている。直感的には、帰納型の項は各コンストラクタによって網羅的に生成され、帰納型はコンストラクタが構築する項以外の項を持たないということである。

``Weekday`` から自然数への関数を定義するには、``match`` 文を使うことができる:

```lean
# inductive Weekday where
#  | sunday : Weekday
#  | monday : Weekday
#  | tuesday : Weekday
#  | wednesday : Weekday
#  | thursday : Weekday
#  | friday : Weekday
#  | saturday : Weekday
open Weekday

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

#eval numberOfDay Weekday.sunday  -- 1
#eval numberOfDay Weekday.monday  -- 2
#eval numberOfDay tuesday         -- 3
```

``match`` 式は帰納型を宣言したときに生成された再帰子 ``Weekday.rec`` を使ってコンパイルされることに注意してほしい。

```lean
# inductive Weekday where
#  | sunday : Weekday
#  | monday : Weekday
#  | tuesday : Weekday
#  | wednesday : Weekday
#  | thursday : Weekday
#  | friday : Weekday
#  | saturday : Weekday
open Weekday

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

set_option pp.all true    -- 詳細な情報を表示させるオプション
#print numberOfDay
-- 定義中に``numberOfDay.match_1``というものが現れている
#print numberOfDay.match_1
-- 定義中に``Weekday.casesOn``というものが現れている
#print Weekday.casesOn
-- 定義中に``Weekday.rec``というものが現れている
#check @Weekday.rec
/-
@Weekday.rec.{u}
 : {motive : Weekday → Sort u} →
    motive Weekday.sunday →
    motive Weekday.monday →
    motive Weekday.tuesday →
    motive Weekday.wednesday →
    motive Weekday.thursday →
    motive Weekday.friday →
    motive Weekday.saturday →
    (t : Weekday) → motive t
-/
```

帰納データ型を宣言するとき、``deriving Repr`` と書くと、``Weekday`` の項をテキストに変換する関数を生成するようLeanに指示することができる。``#eval`` コマンドはこの関数を使って ``Weekday`` の項を表示する。

```lean
inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  deriving Repr

open Weekday

#eval tuesday   -- Weekday.tuesday (``deriving Repr`` を外すとエラーになる)
```

ある帰納型に関連する定義や定理を、型と同じ名前の名前空間にまとめると便利なことが多い。例えば、``numberOfDay`` 関数を ``Weekday`` 名前空間に置くとよい。そうすると、名前空間 ``Weekday`` を開いたときに、コンストラクタにも定義・定理・関数にも短い名前を用いてアクセスすることができる。

``Weekday`` から ``Weekday`` への関数を定義することができる:

```lean
# inductive Weekday where
#  | sunday : Weekday
#  | monday : Weekday
#  | tuesday : Weekday
#  | wednesday : Weekday
#  | thursday : Weekday
#  | friday : Weekday
#  | saturday : Weekday
#  deriving Repr
namespace Weekday
def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def previous (d : Weekday) : Weekday :=
  match d with
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

#eval next (next tuesday)      -- Weekday.thursday
#eval next (previous tuesday)  -- Weekday.tuesday

example : next (previous tuesday) = tuesday :=
  rfl

end Weekday
```

どうすればより一般的な定理「任意のWeekday ``d`` に対して、``next (previous d) = d``」が証明できるだろうか。``match`` を使うと各コンストラクタに対して主張の証明を与えることができる:

```lean
# inductive Weekday where
#  | sunday : Weekday
#  | monday : Weekday
#  | tuesday : Weekday
#  | wednesday : Weekday
#  | thursday : Weekday
#  | friday : Weekday
#  | saturday : Weekday
#  deriving Repr
# namespace Weekday
# def next (d : Weekday) : Weekday :=
#  match d with
#  | sunday    => monday
#  | monday    => tuesday
#  | tuesday   => wednesday
#  | wednesday => thursday
#  | thursday  => friday
#  | friday    => saturday
#  | saturday  => sunday
# def previous (d : Weekday) : Weekday :=
#  match d with
#  | sunday    => saturday
#  | monday    => sunday
#  | tuesday   => monday
#  | wednesday => tuesday
#  | thursday  => wednesday
#  | friday    => thursday
#  | saturday  => friday
theorem next_previous (d : Weekday) : next (previous d) = d :=
  match d with
  | sunday    => rfl
  | monday    => rfl
  | tuesday   => rfl
  | wednesday => rfl
  | thursday  => rfl
  | friday    => rfl
  | saturday  => rfl
```

タクティク証明を使えば、定理 ``next_previous`` の証明はより簡潔になる:

```lean
# inductive Weekday where
#  | sunday : Weekday
#  | monday : Weekday
#  | tuesday : Weekday
#  | wednesday : Weekday
#  | thursday : Weekday
#  | friday : Weekday
#  | saturday : Weekday
#  deriving Repr
# namespace Weekday
# def next (d : Weekday) : Weekday :=
#  match d with
#  | sunday    => monday
#  | monday    => tuesday
#  | tuesday   => wednesday
#  | wednesday => thursday
#  | thursday  => friday
#  | friday    => saturday
#  | saturday  => sunday
# def previous (d : Weekday) : Weekday :=
#  match d with
#  | sunday    => saturday
#  | monday    => sunday
#  | tuesday   => monday
#  | wednesday => tuesday
#  | thursday  => wednesday
#  | friday    => thursday
#  | saturday  => friday
def next_previous (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl
```

以下の節 [Tactics for Inductive Types (帰納型のためのタクティク)](#tactics-for-inductive-types-帰納型のためのタクティク) では、帰納型を利用するのに特化したタクティクを紹介する。

「型としての命題対応」の下では、定理証明と関数定義の両方に ``match`` を使えることに注目してほしい。言い換えれば、「型としての命題対応」の下では、場合分けによる証明は場合分けによる定義の一種なのである。そこには「定義」されるものが「データ型の項」なのか「命題型の証明」なのかの違いしかない。

Leanのライブラリにおいて、``Bool`` 型は列挙型の一例である。

```lean
# namespace Hidden
inductive Bool where
  | false : Bool
  | true  : Bool
# end Hidden
```

(この例において、標準ライブラリ内の ``Bool`` と今定義する ``Bool`` の衝突を防ぐために、今定義する ``Bool`` を名前空間 ``Hidden`` の中に置いた。この処置は必須である。なぜなら、``Bool`` はLeanの標準ライブラリ内の最初のファイル ``Init/Prelude.lean`` の一部であり、Leanが起動したときに自動的にインポートされるからである。)

練習として、「``Bool`` 型の導入則と除去則は何か」を考えるといいだろう。発展問題として、名前空間 ``Hidden`` の中で、自分の手で ``Bool`` 型と ``Bool`` 型上の演算子(ブーリアン演算子) ``and``、``or``、``not`` を定義し、それらに関する基本的な恒等式を証明してみることをお勧めする。``and`` のような2項演算子は ``match`` を使って定義できることに注目してほしい:

```lean
# namespace Hidden
def and (a b : Bool) : Bool :=
  match a with
  | true  => b
  | false => false
# end Hidden
```

同様に、ほとんどの恒等式は適切に ``match`` を使ってから ``rfl`` を使うことで証明できる。

## Constructors with Arguments (引数を持つコンストラクタ)

列挙型は、そのコンストラクタが全く引数を取らないという点で帰納型の非常に特殊な例である。一般的に、コンストラクタは入力データ(引数)を使って項を構築することができる。ライブラリ内の直積型と直和型の定義について考えてみよう:

```lean
# namespace Hidden
inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β

inductive Sum (α : Type u) (β : Type v) where
  | inl : α → Sum α β
  | inr : β → Sum α β
# end Hidden
```

この例の中で何が起きているか考えてみよう。直積型は唯一のコンストラクタ ``Prod.mk`` を持ち、これは2つの引数を取る。``Prod α β`` 型の項を引数にとる関数を定義するには、入力が ``Prod.mk a b`` の形であると仮定し、``a`` と ``b`` を用いて出力を指定する必要がある。この関数定義法は ``Prod α β`` 型の項のための2つの射影を定義する際にも使える。標準ライブラリにおいて、記法 ``α × β`` は ``Prod α β`` を表し、``(a, b)`` は ``Prod.mk a b`` を表すことを覚えてほしい。

```lean
# namespace Hidden
# inductive Prod (α : Type u) (β : Type v)
#   | mk : α → β → Prod α β
def fst {α : Type u} {β : Type v} (p : Prod α β) : α :=
  match p with
  | Prod.mk a b => a

def snd {α : Type u} {β : Type v} (p : Prod α β) : β :=
  match p with
  | Prod.mk a b => b
# end Hidden
```

関数 ``fst`` はペア ``p`` を受け取る。``match`` は ``p`` をペア ``Prod.mk a b`` として解釈する。[2章 Dependent Type Theory (依存型理論)](./dependent_type_theory.md)において、これらの定義に出来るだけ強い普遍性を与えるには、型 ``α`` と ``β`` がどの型宇宙に属していてもよいように定義を書く必要がある、と学んだことを思い出してほしい。

以下は ``match`` の代わりに再帰子 ``Prod.casesOn`` を使った例である。

```lean
def prod_example (p : Bool × Nat) : Nat :=
  Prod.casesOn (motive := fun _ => Nat) p (fun b n => cond b (2 * n) (2 * n + 1))

#eval prod_example (true, 3)
#eval prod_example (false, 3)
```

引数 ``motive`` は構築したい項の型を指定するために使われる。そして、構築したい項の型は入力データ(この場合はペア)に依存して変わりうるので、``motive`` は関数である。``cond`` 関数はブール値を用いた条件分岐を実現する: ``cond b t1 t2`` は ``b`` が真なら ``t1`` を返し、そうでなければ ``t2`` を返す。上記の例で、関数 ``prod_example`` はブール値 ``b`` と自然数 ``n`` を取り、``b`` が真なら ``2 * n`` を返し、``b`` が偽なら ``2 * n + 1`` を返す。

対照的に、直和型は**2つの**コンストラクタ ``inl`` と ``inr`` ("insert left"と"insert right"の略) を持ち、それぞれは**1つの**(明示的な)引数を取る。``Sum α β`` 型の項を引数にとる関数を定義するには、2つの場合に対応しなければならない: 入力が ``inl a`` の形なら ``a`` を使って出力する値を指定する必要がある。入力が ``inr b`` の形なら ``b`` を使って出力する値を指定する必要がある。

```lean
def sum_example (s : Sum Nat Nat) : Nat :=
  Sum.casesOn (motive := fun _ => Nat) s
    (fun n => 2 * n)
    (fun n => 2 * n + 1)

#eval sum_example (Sum.inl 3)
#eval sum_example (Sum.inr 3)

def sum_example2 (s : Sum Nat Nat) : Nat :=
  match s with
  | Sum.inl a => 2 * a
  | Sum.inr b => 2 * b + 1

#eval sum_example2 (Sum.inl 3)
#eval sum_example2 (Sum.inr 3)
```

この例は1つ前の例に似ている。しかし、この例では ``sum_example`` への入力は暗黙的に ``inl n`` か ``inr n`` のいずれかの形をとる。1つ目の場合なら関数は ``2 * n`` を返し、2つ目の場合なら関数は ``2 * n + 1`` を返す。

直積型は引数 ``α β : Type`` を持つことに注意してほしい。これらは ``Prod`` の引数であると同時に、``Prod`` のコンストラクタの引数の型でもある。引数 ``α β`` がコンストラクタへの後続の引数や戻り値の型から推論できる場合、Leanは引数 ``α β`` が何であるかを特定し、それらを暗黙の引数にする。

[Defining the Natural Numbers (自然数を定義する)](#defining-the-natural-numbers-自然数を定義する)の節では、帰納型のコンストラクタがその帰納型自体の項を引数として取るときに何が起こるかを説明する。その節で考える例の特徴は、各コンストラクタが当該型の項として既に特定された項のみを引数として取ることである。

複数のコンストラクタを持つ型は「選言的」であることに注意してほしい: ``Sum α β`` の項は ``inl a`` **または** ``inr b`` の形をしている。複数の引数を取るコンストラクタは「連言的」な情報を提供する: ``Prod α β`` の項 ``Prod.mk a b`` からは ``a`` **と** ``b`` を抽出することができる。任意の帰納型は、任意個のコンストラクタを持つことができ、各コンストラクタは任意個の引数を取ることができるので、選言的かつ連言的な特徴を持つ可能性がある。

関数定義と同様に、Leanの帰納型定義構文内では、コンストラクタ名とコロンの間に名前付き引数を与えることができる:

```lean
# namespace Hidden
inductive Prod (α : Type u) (β : Type v) where
  | mk (fst : α) (snd : β) : Prod α β

inductive Sum (α : Type u) (β : Type v) where
  | inl (a : α) : Sum α β
  | inr (b : β) : Sum α β
# end Hidden
```

これらの定義は上で与えた定義と本質的に同じである。

``Prod`` のように、ただ1つのコンストラクタを持つ型は純粋に連言的である: そのコンストラクタは単に引数のリストを1つのデータにまとめる。このようなデータは後続の要素の型が最初の要素の型に依存することができるタプルと本質的に同じである。このような型は*record*(レコード)あるいは*structure*(構造体)と呼ばれる。Leanでは、キーワード ``structure`` を使うと、レコードや構造体の定義とその射影の定義を同時に行うことができる。

```lean
# namespace Hidden
structure Prod (α : Type u) (β : Type v) where
  mk :: (fst : α) (snd : β)
# end Hidden
```

この例では、帰納型 ``Prod``、そのコンストラクタ ``mk``、通常のエリミネータ(``rec`` と ``recOn``)と射影 ``fst`` と ``snd`` (上で定義したものと同じ)を同時に定義している。

コンストラクタに名前を付けなかった場合、デフォルトのコンストラクタの名前として ``mk`` が使われる。次の例は、RGB値の3つ組として色を保存するレコードを定義する:

```lean
structure Color where
  (red : Nat) (green : Nat) (blue : Nat)
  deriving Repr

def yellow := Color.mk 255 255 0

#print Color.red  -- ``structure`` キーワードにより生成された射影関数
#eval Color.red yellow
```

``yellow`` の定義は3つの値を持ったレコードを形成する。そして射影 ``Color.red`` は赤の要素を返す。

各フィールドの間に改行を挟めば、括弧の使用を避けることができる。

```lean
structure Color where
  red : Nat
  green : Nat
  blue : Nat
  deriving Repr
```

``structure`` コマンドは代数的構造を定義するときに特に有用である。Leanは代数的構造を扱うための実質的なインフラを提供している。例えば、以下は半群の定義である:

```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
```

[9章 Structures and Records](./structures_and_records.md)ではさらに例を見ていく。

依存直積型 ``Sigma`` は既に紹介した:

```lean
# namespace Hidden
inductive Sigma {α : Type u} (β : α → Type v) where
  | mk : (a : α) → β a → Sigma β
# end Hidden
```

次はライブラリ内にあるさらに2つの帰納型の例である:

```lean
# namespace Hidden
inductive Option (α : Type u) where
  | none : Option α
  | some : α → Option α

inductive Inhabited (α : Type u) where
  | mk : α → Inhabited α
# end Hidden
```

依存型理論の意味論では、全ての関数は全域関数である。関数型 ``α → β`` または依存関数型 ``(a : α) → β`` の各項は、全ての入力に対して一意の値を持つと想定される。したがって、依存型理論の意味論に部分関数の概念は組み込まれていない。しかし、``Option`` 型を使うと(全域関数を使って)部分関数を表現することができる。``Option β`` の項は、``none`` か ``some b``(ここで、``b : β``) の形をとる。したがって、``α → Option β`` 型の項 ``f`` は、``α`` から ``β`` への部分関数であると考えることができる: 任意の ``a : α`` に対して、``f a`` は ``none`` か ``some b`` を返す。``none`` は ``f a`` が「未定義」であることを表す。

``Inhabited α`` の項は、単に ``α`` の項が存在することの証人となる。後ほど、Leanにおいて ``Inhabited`` が*type class*(型クラス)の一例であることを説明する: Leanに適切な基底型が*inhabited*(有項)であると指示することができる。Leanはその指示に基づいて、他の構築された型が有項であることを自動的に推論することができる。

練習として、``α`` から ``β`` への部分関数と ``β`` から ``γ`` への部分関数の合成の概念を定義し、それが期待通りの振る舞いをすることを示すことを勧める。また、``Bool`` と ``Nat`` が有項であること、2つの有項な型の直積型が有項であること、有項な型への関数の型は有項であることを示すことも勧める。

## Inductively Defined Propositions (帰納的に定義された命題)

帰納的に定義された型は、一番下の型である ``Prop`` を含め、どの階層の型宇宙にも住むことができる。実際、論理的結合子は次のように定義されている。

```lean
# namespace Hidden
inductive False : Prop

inductive True : Prop where
  | intro : True

inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b
# end Hidden
```

これらの定義が、すでに見た論理的結合子の導入則と除去則をどのように生み出すのかを考える必要がある。帰納型のエリミネータがその型を除去して**何の型を作れるか**を規定するルールがある。つまり、どのような型を再帰子の対象とすることができるかを規定するルールがある。大雑把に言えば、``Prop`` に属する帰納型には、その型を除去することで ``Prop`` に属する他の型しか作ることができないというルールがある。これは、「もし ``p : Prop``なら、``hp : p`` は何のデータも持たない」という理解と矛盾しない。しかしながら、[Inductive Families (帰納族)](#inductive-families-帰納族)の節で説明するように、このルールには小さな例外がある。

存在量化子でさえ帰納的に定義されている:

```lean
# namespace Hidden
inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p
# end Hidden
```

記法 ``∃ x : α, p`` は ``Exists (fun x : α => p)`` の糖衣構文であることを思い出してほしい。

``False``、``True``、``And``、``Or`` の定義は、``Empty``、``Unit``、``Prod``、``Sum`` の定義と完全に類似している。違いは、最初のグループは ``Prop`` の項を生成し、2番目のグループはある宇宙パラメータ ``u`` に対して ``Type u`` の項を生成することである。同様に、``∃ x : α, p`` と ``Σ x : α, p`` は類似しているが、前者は ``Prop`` の項で、後者は ``Type u`` の項である。

もうひとつの帰納型 ``{x : α // p}`` に触れる良い機会だろう。これは、``∃ x : α, P`` と ``Σ x : α, P`` のハイブリッドのようなものである。

```lean
# namespace Hidden
inductive Subtype {α : Type u} (p : α → Prop) where
  | mk : (x : α) → p x → Subtype p
# end Hidden
```

実際には、Leanでは ``Subtype`` は ``structure`` コマンドを使って定義されている:

```lean
# namespace Hidden
structure Subtype {α : Sort u} (p : α → Prop) where
  val : α
  property : p val
# end Hidden
```

記法 ``{x : α // p x}`` は ``Subtype (fun x : α => p x)`` の糖衣構文である。これは集合論における部分集合の内包的表記をモデルにしている: ``{x : α // p x}`` は性質 ``p`` を持つ ``α`` の要素全体からなる集合を表す。

## Defining the Natural Numbers (自然数を定義する)

これまで見てきた帰納型は「フラット」である: コンストラクタはデータ(引数)を包んである型の項を作り、対応する再帰子はその項を展開してそれに作用する。コンストラクタがそのコンストラクタたちによってまさに今帰納的に定義されている型の項を受け取ると、物事はもっと面白くなる。典型的な例が自然数の型 ``Nat`` である:

```lean
# namespace Hidden
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
# end Hidden
```

``Nat`` のコンストラクタは2つある。まずは ``zero : Nat`` から始める。コンストラクタ ``zero`` は引数を取らないので、``Nat`` は最初から項 ``zero`` を持っている。対照的に、コンストラクタ ``succ`` は既に構築された ``Nat`` の項に対してのみ適用できる。これを ``zero`` に適用すると、``succ zero : Nat`` が得られる。もう一度適用すると ``succ (succ zero) : Nat`` が得られる。直感的には、``Nat`` はこのようなコンストラクタを持つ「最小の」型であるといえる。このようなコンストラクタを持つことは、``Nat`` の項は、 ``zero`` から始めて ``succ`` を繰り返し適用することで網羅的に(そして自由に)生成されることを意味する。

以前と同様に、``Nat`` のための再帰子は、``Nat`` から任意の型への依存関数 ``f``、つまりある ``motive : Nat → Sort u`` について ``(n : Nat) → motive n`` の項 ``f`` を定義するように設計されている。再帰子は、入力が ``zero`` の場合と、入力がある ``n : Nat`` について ``succ n`` の形をとる場合の2種類の場合に対応しなければならない。最初のケースでは、先ほどと同じように、適切な型を持つ出力値を指定するだけでよい。2番目のケースはそうはいかない。しかし、2番目のケースでは、再帰子は ``n`` における ``f`` の値がすでに計算されていると想定することができる。その結果、再帰子の次の引数は ``n`` と ``f n`` を用いて ``f (succ n)`` の値を指定する。再帰子 ``Nat.rec`` の型をチェックしてみると、

```lean
# namespace Hidden
# inductive Nat where
#  | zero : Nat
#  | succ : Nat → Nat
#check @Nat.rec
# end Hidden
```

次のような表示が得られる:

```
  {motive : Nat → Sort u}
  → motive Nat.zero
  → ((n : Nat) → motive n → motive (Nat.succ n))
  → (t : Nat) → motive t
```

暗黙の引数 ``motive`` は、定義される関数のコドメインである。型理論では、``motive`` は除去/再帰の*motive*(動機)であると言うのが一般的である。それは ``motive t`` が入力 ``t`` に対して構築したい項の型を表しているからである。``motive`` の次の2つの引数は、上述した2つの場合、つまり入力が ``zero`` の場合と ``succ n`` の形をとる場合の計算方法をそれぞれ指定する。この2つの引数は*minor premises*(小前提)としても知られている。最後に、``t : Nat`` は定義したい関数への入力である。入力 ``t`` は*major premise*(大前提)としても知られている。 

``Nat.recOn`` は ``Nat.rec`` とほとんど同じだが、大前提が小前提の前に現れている。

```
@Nat.recOn :
  {motive : Nat → Sort u}
  → (t : Nat)
  → motive Nat.zero
  → ((n : Nat) → motive n → motive (Nat.succ n))
  → motive t
```

例えば、自然数に対する加法関数 ``add m n`` を定義することを考えてみよう。``m`` を固定すると、``n`` に関する再帰によって加法を定義することができる。base caseでは、``add m zero`` を ``m`` と定義する。successor stepでは、``add m n`` の値が既に決定されていると仮定して、``add m (succ n)`` を ``succ (add m n)`` と定義する。

```lean
# namespace Hidden
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
  deriving Repr

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

open Nat

#eval add (succ (succ zero)) (succ zero)
# end Hidden
```

このような関数定義は名前空間 ``Nat`` に入れておくと便利である。それから、その名前空間の中でお馴染みの記法 ``+`` を定義することができる。ここまですると、加法に関する2つの等式が成立することが定義により示せる:

```lean
# namespace Hidden
# inductive Nat where
#  | zero : Nat
#  | succ : Nat → Nat
#  deriving Repr
namespace Nat

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

instance : Add Nat where
  add := add

theorem add_zero (m : Nat) : m + zero = m := rfl
theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := rfl

end Nat
# end Hidden
```

``instance`` コマンドがどのように機能するかは、[10章 Type Classes (型クラス)](./type_classes.md)で説明する。以下の例では、Leanの標準ライブラリで定義された自然数を使う。

上記では ``rfl`` を使うだけで定理が証明できた。しかし、``zero + m = m`` のような定理は帰納法による証明を必要とする。上述の通り、帰納法の原理は再帰の原理の特殊な場合にすぎない。帰納法において、``motive n`` のコドメインは一般的な型 ``Sort u`` ではなく ``Prop`` である。これは帰納法による証明のお馴染みのパターンを表現している: ``∀ n, motive n`` を証明するために、まず ``motive 0`` を証明する。次に任意の ``n : Nat`` について ``ih : motive n`` を仮定し、その上で ``motive (succ n)`` を証明する。

```lean
# namespace Hidden
open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x)
   n
   (show 0 + 0 = 0 from rfl)
   (fun (n : Nat) (ih : 0 + n = n) =>
    show 0 + succ n = succ n from
    calc 0 + succ n
      _ = succ (0 + n) := rfl
      _ = succ n       := by rw [ih])
# end Hidden
```

繰り返しになるが、証明内で ``Nat.recOn`` を使うことは、証明内で帰納法の原理を使うことを意味することに注意してほしい。このような証明において、``rewrite`` タクティクと ``simp`` タクティクは非常に効果的である。今回の場合、``simp`` タクティクを使うと次のように証明を短くすることができる:

```lean
# namespace Hidden
open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x) n
    rfl
    (fun n ih => by simp [add_succ, ih])
# end Hidden
```

もう一つの例として、加法の結合性 ``∀ m n k, m + n + k = m + (n + k)`` を証明しよう。ここで、``+`` という記法は左結合的なので、``m + n + k`` とは ``(m + n) + k`` のことである。一番難しいのは、どの変数に関して帰納法を行うかの見当をつけることだ。加法は2番目の引数に関する再帰によって定義されるため、``k`` を選ぶのはよい判断である。一度変数を選択すれば、証明はほとんど自ずと導かれる:

```lean
# namespace Hidden
open Nat
theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    (show m + n + 0 = m + (n + 0) from rfl)
    (fun k (ih : m + n + k = m + (n + k)) =>
      show m + n + succ k = m + (n + succ k) from
      calc m + n + succ k
        _ = succ (m + n + k)   := rfl
        _ = succ (m + (n + k)) := by rw [ih]
        _ = m + succ (n + k)   := rfl
        _ = m + (n + succ k)   := rfl)
# end Hidden
```

再び、``simp`` タクティクを使って証明を短くすることができる:

```lean
open Nat
theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    rfl
    (fun k ih => by simp [Nat.add_succ, ih])
```

次は加法の可換性を証明してみよう。2番目の引数に関して帰納法を行うことを選択すると、次のように証明を始めることができる:

```lean
open Nat
theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
   (show m + 0 = 0 + m by rw [Nat.zero_add, Nat.add_zero])
   (fun (n : Nat) (ih : m + n = n + m) =>
    show m + succ n = succ n + m from
    calc m + succ n
      _ = succ (m + n) := rfl
      _ = succ (n + m) := by rw [ih]
      _ = succ n + m   := sorry)
```

ここで、もう1つの補題 ``succ n + m = succ (n + m)`` が必要であるとわかる。これは ``m`` に関する帰納法で証明できる:

```lean
open Nat

theorem succ_add (n m : Nat) : succ n + m = succ (n + m) :=
  Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
    (show succ n + 0 = succ (n + 0) from rfl)
    (fun (m : Nat) (ih : succ n + m = succ (n + m)) =>
     show succ n + succ m = succ (n + succ m) from
     calc succ n + succ m
       _ = succ (succ n + m)   := rfl
       _ = succ (succ (n + m)) := by rw [ih]
       _ = succ (n + succ m)   := rfl)
```

それから、上記の証明の ``sorry`` を ``succ_add`` に置き換えて、証明を完結させることができる。再び、これらの証明は短くできる:

```lean
# namespace Hidden
open Nat
theorem succ_add (n m : Nat) : succ n + m = succ (n + m) :=
  Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
    rfl
    (fun m ih => by simp only [add_succ, ih])

theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
    (by simp)
    (fun m ih => by simp [add_succ, succ_add, ih])
# end Hidden
```

## Other Recursive Data Types (他の再帰データ型)

帰納的に定義された型の例をもう少し考えてみよう。任意の型 ``α`` に対して、いくつかの ``α`` の項からなるリストの型 ``List α`` がライブラリで定義されている。

```lean
# namespace Hidden
inductive List (α : Type u) where
  | nil  : List α
  | cons : α → List α → List α

namespace List

def append (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as :=
  rfl

theorem cons_append (a : α) (as bs : List α)
                    : append (cons a as) bs = cons a (append as bs) :=
  rfl

end List
# end Hidden
```

``α`` 型の項を要素に持つリストは、空リスト ``nil`` か ``cons h t`` の形をとるかのいずれかである。ここで、``cons h t`` は項 ``h : α`` の後にリスト ``t : List α`` が続くリストである。最初の要素 ``h`` は一般にリストの"head"と呼ばれ、残りの要素 ``t`` は"tail"と呼ばれる。

練習問題として、以下の定理を証明せよ:

```lean
# namespace Hidden
# inductive List (α : Type u) where
# | nil  : List α
# | cons : α → List α → List α
# namespace List
# def append (as bs : List α) : List α :=
#  match as with
#  | nil       => bs
#  | cons a as => cons a (append as bs)
# theorem nil_append (as : List α) : append nil as = as :=
#  rfl
# theorem cons_append (a : α) (as bs : List α)
#                     : append (cons a as) bs = cons a (append as bs) :=
#  rfl
theorem append_nil (as : List α) : append as nil = as :=
  sorry

theorem append_assoc (as bs cs : List α)
        : append (append as bs) cs = append as (append bs cs) :=
  sorry
# end List
# end Hidden
```

また、リストの長さを返す関数 ``length : {α : Type u} → List α → Nat`` を定義せよ。さらにそれが期待通りに振る舞うことを証明せよ。例えば、``length (append as bs) = length as + length bs`` を証明せよ。

別の例として、binary trees((全)二分木)の型を定義することができる:

```lean
/- 1. ただ1つの頂点からなる有向グラフは全二分木である。
   2. 次数0の頂点vと2つの全二分木A,Bを用意し、
   ラベル付き有向辺(左,v,Aの根)と(右,v,Bの根)を追加し、vを根としたものは全二分木である。
   3. 以上の手続きで全二分木だとわかるものだけが全二分木である。 -/
inductive BinaryTree where
  | leaf : BinaryTree
  | root (left : BinaryTree) (right : BinaryTree) : BinaryTree
```

countably branching trees((全)可算無限分木)の型を定義することさえできる:

```lean
/- 1. ただ1つの頂点からなる有向グラフは全可算無限分木である。
   2. 次数0の頂点vと2つの全可算無限分木T_0,T_1,...を用意し、
   ラベル付き有向辺(0,v,T_0の根),(1,v,T_1の根),...を追加し、vを根としたものは全可算無限分木である。
   3. 以上の手続きで全可算無限分木だとわかるものだけが全可算無限分木である。 -/
inductive CBTree where
  | leaf : CBTree
  | sup : (Nat → CBTree) → CBTree

namespace CBTree

def succ (t : CBTree) : CBTree :=
  sup (fun _ => t)

def toCBTree : Nat → CBTree
  | 0 => leaf
  | n+1 => succ (toCBTree n)

def omega : CBTree :=
  sup toCBTree

end CBTree
```

## Tactics for Inductive Types (帰納型のためのタクティク)

Leanにおける帰納型の基礎的な重要性を鑑みれば、帰納型を効率的に扱うためにデザインされたタクティクが数多くあることは驚くことではない。ここではそのようなタクティクのいくつかを紹介する。

``cases`` タクティクは帰納的に定義された型の項に対して機能し、その名前が示す通りの働きをする: ``cases`` タクティクは存在する各コンストラクタに従って項を分解する。最も基本的な形では、``cases`` タクティクは現在のコンテキスト内の項 ``x`` に適用される。そして、``x`` を各コンストラクタで置換して、ゴールを場合分けする。

```lean
example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (Nat.succ n)) : ∀ n, p n := by
  intro n
  cases n
  . exact hz  -- goal is p 0
  . apply hs  -- goal is a : Nat ⊢ p (succ a)
```

さらに便利な機能がある。まず、``with`` キーワードを使うと、``cases`` タクティク使用時の各場合分けにおいて変数に名前を付けることができる。次の例では、``succ`` の引数に ``m`` という名前を付け、2番目の場合で ``n`` を ``succ m`` で置換するように指示している。さらに重要なのは、``cases`` タクティクが、現在のコンテキスト内にある、場合分け対象の変数に依存する型を持つ項を検出することである。``cases`` タクティクはこれらの項をゴールのターゲットに戻し、ゴールを場合分けし、再び項をゴールのコンテキストに導入する。次の例では、仮説 ``h : n ≠ 0`` が最初の分岐では ``h : 0 ≠ 0`` になり、2番目の分岐では ``h : succ m ≠ 0`` になることに注目してほしい。

```lean
open Nat

example (n : Nat) (h : n ≠ 0) : succ (pred n) = n := by
  cases n with
  | zero =>
    -- goal: h : 0 ≠ 0 ⊢ succ (pred 0) = 0
    apply absurd rfl h
  | succ m =>
    -- second goal: h : succ m ≠ 0 ⊢ succ (pred (succ m)) = succ m
    rfl
```

``cases`` は命題を証明するだけでなく、データを生成するためにも使用できることに注目してほしい。

```lean
def f (n : Nat) : Nat := by
  cases n; exact 3; exact 7

example : f 0 = 3 := rfl
example : f 5 = 7 := rfl
```

繰り返しになるが、``cases x`` はコンテキスト内にある ``x`` に依存する型を持つ項をターゲットに戻し、ゴールを場合分けし、再び項をコンテキストに導入する。

```lean
def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

def f {n : Nat} (t : Tuple α n) : Nat := by
  cases n; exact 3; exact 7

def myTuple : Tuple Nat 3 :=
  ⟨[0, 1, 2], rfl⟩

example : f myTuple = 7 :=
  rfl
```

次は引数をとる複数のコンストラクタを持つ帰納型における例である。

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x with
  | bar1 a b => exact b
  | bar2 c d e => exact e

#eval silly (Foo.bar1 1 2)    -- 2
#eval silly (Foo.bar2 3 4 5)  -- 5
```

各コンストラクタによって生成された各ゴールは、帰納型の定義におけるコンストラクタの宣言順に解く必要はない。

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x with
  | bar2 c d e => exact e
  | bar1 a b => exact b
```

``with`` の構文は構造化された証明を書くのに便利である。また、Leanは ``cases`` を補完する ``case`` タクティクを提供する。これを使うと、各ケースで変数名を割り当てることに集中することができる。

```lean
# inductive Foo where
#   | bar1 : Nat → Nat → Foo
#   | bar2 : Nat → Nat → Nat → Foo
def silly (x : Foo) : Nat := by
  cases x
  case bar1 a b => exact b
  case bar2 c d e => exact e
```

``case`` タクティクは賢く、各コンストラクタを適切なゴールにマッチさせることができる。例えば、上記のゴールを逆順で埋めることができる:

```lean
# inductive Foo where
#   | bar1 : Nat → Nat → Foo
#   | bar2 : Nat → Nat → Nat → Foo
def silly (x : Foo) : Nat := by
  cases x
  case bar2 c d e => exact e
  case bar1 a b => exact b
```

さらに、任意の式 ``e`` に対して ``cases e`` を使うこともできる。もしその式がゴールのターゲットに現れるなら、``cases`` タクティクはその式を一般化し、その結果生じる全称量化された変数を導入し、その上でゴールを場合分けする。

```lean
open Nat

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  cases m + 3 * k
  . exact hz   -- goal is p 0
  . apply hs   -- goal is a : Nat ⊢ p (succ a)
```

これは、「(``m + 3 * k`` は自然数なので、)``m + 3 * k`` が0か、ある数の後者かで場合分けする」と言っているのだと考えてほしい。この結果は機能的には次の例と等価である:

```lean
open Nat

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  generalize m + 3 * k = n
  cases n
  . exact hz   -- goal is p 0
  . apply hs   -- goal is a : Nat ⊢ p (succ a)
```

式 ``m + 3 * k`` は ``generalize`` によって消去されることに注意してほしい; 重要なのは、それが ``0`` か ``succ a`` のどちらの形式を持つかだけである。 この使い方の場合、``cases`` は等式(この場合は ``m + 3 * k = n``)中の項について言及している仮説をゴールのターゲットに戻さ**ない**。そのような仮説がコンテキストの中にあり、それについても一般化したい場合は、明示的にそれを ``revert`` で戻す必要がある。

場合分けの対象となる式がゴールのターゲット内にない場合、``cases`` タクティクは ``have`` を使い、分解後の式を型として持つ項をコンテキストに導入する。以下はその例である:

```lean
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  cases Nat.lt_or_ge m n
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge
```

``Nat.lt_or_ge m n`` とは ``m < n ∨ m ≥ n`` の証明項であり、上の証明はこの2つの場合に分かれると考えるのが自然である。最初の分岐では仮説 ``hlt : m < n`` を持つ。2番目の分岐では仮説 ``hge : m ≥ n`` を持つ。上の証明は、機能的には次と等価である:

```lean
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  have h : m < n ∨ m ≥ n := Nat.lt_or_ge m n
  cases h
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge
```

``have`` タクティクにより仮説 ``h : m < n ∨ m ≥ n`` が得られるので、その仮説に対して ``cases`` を適用する。

次の例では、自然数における等式の決定可能性を利用して、``m = n`` と ``m ≠ n`` の場合に分けて証明する。

```lean
#check Nat.sub_self

theorem t1 (m n : Nat) : m - n = 0 ∨ m ≠ n := by
  cases Decidable.em (m = n) with
  | inl heq => rw [heq]; apply Or.inl; exact Nat.sub_self n
  | inr hne => apply Or.inr; exact hne

/- ``Decidable.em`` は排中律 ``Classical.em`` を必要としない -/
#print axioms t1  -- 't1' does not depend on any axioms
```

``open Classical`` を使えば、任意の命題に対して排中律 ``em`` が使えることを思い出してほしい。しかし、型クラス推論([10章 Type Classes (型クラス)](./type_classes.md)を参照)を使えば、Leanは排中律に似て非なる決定手続きを見つけることができる。つまり、計算可能関数において場合分け ``p ∨ ¬p`` を使うことができるのである。

``cases`` タクティクが場合分けによる証明を行うのに使えるように、``induction`` タクティクは帰納法による証明を行うのに使える。``induction`` タクティクの構文は ``cases`` タクティクの構文と似ているが、前者は引数が現在のコンテキストの項でなければならない点が異なる。以下はその例である:

```lean
# namespace Hidden
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]
# end Hidden
```

``cases`` と同様に、``induction`` タクティクでは ``with`` キーワードの代わりに ``case`` タクティクを使うことができる。

```lean
# namespace Hidden
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ n ih => rw [Nat.add_succ, ih]
# end Hidden
```

以下に例を追加する:

```lean
# namespace Hidden
# theorem add_zero (n : Nat) : n + 0 = n := Nat.add_zero n
open Nat

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n <;> simp [*, add_zero, add_succ]

theorem succ_add (m n : Nat) : succ m + n = succ (m + n) := by
  induction n <;> simp [*, add_zero, add_succ]

theorem add_comm (m n : Nat) : m + n = n + m := by
  induction n <;> simp [*, add_zero, add_succ, succ_add, zero_add]

theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) := by
  induction k <;> simp [*, add_zero, add_succ]
# end Hidden
```

``induction`` タクティクは複数の引数(大前提)をとるユーザー定義の帰納法原理もサポートしている。

```lean
/-
theorem Nat.mod.inductionOn
      {motive : Nat → Nat → Sort u}
      (x y  : Nat)
      (ind  : ∀ x y, 0 < y ∧ y ≤ x → motive (x - y) y → motive x y)
      (base : ∀ x y, ¬(0 < y ∧ y ≤ x) → motive x y)
      : motive x y :=
-/

example (x : Nat) {y : Nat} (h : y > 0) : x % y < y := by
  induction x, y using Nat.mod.inductionOn with
  | ind x y h₁ ih =>
    rw [Nat.mod_eq_sub_mod h₁.2]
    exact ih h
  | base x y h₁ =>
    have : ¬ 0 < y ∨ ¬ y ≤ x := Iff.mp (Decidable.not_and_iff_or_not ..) h₁
    match this with
    | Or.inl h₁ => exact absurd h h₁
    | Or.inr h₁ =>
      have hgt : y > x := Nat.gt_of_not_le h₁
      rw [← Nat.mod_eq_of_lt hgt] at hgt
      assumption
```

タクティク証明の中で ``match`` 記法を使うこともできる:

```lean
example : p ∨ q → q ∨ p := by
  intro h
  match h with
  | Or.inl _  => apply Or.inr; assumption
  | Or.inr h2 => apply Or.inl; exact h2
```

便利なことに、パターンマッチングは ``intro`` や ``funext`` のようなタクティクに統合されている。

```lean
example : s ∧ q ∧ r → p ∧ r → q ∧ p := by
  intro ⟨_, ⟨hq, _⟩⟩ ⟨hp, _⟩
  exact ⟨hq, hp⟩

example :
    (fun (x : Nat × Nat) (y : Nat × Nat) => x.1 + y.2)
    =
    (fun (x : Nat × Nat) (z : Nat × Nat) => z.2 + x.1) := by
  funext (a, b) (c, d)
  show a + d = d + a
  rw [Nat.add_comm]
```

最後に、``injection`` タクティクを紹介してセクションを閉じる。このタクティクは帰納型を扱いやすくするためにデザインされている。Leanの設計上、帰納型の項は自由に生成される。つまり、各コンストラクタは単射であり、各コンストラクタの値域は互いに交わりを持たない。``injection`` タクティクはこの事実を利用するようにデザインされている:

```lean
open Nat

example (m n k : Nat) (h : succ (succ m) = succ (succ n))
        : n + k = m + k := by
  injection h with h'
  injection h' with h''
  rw [h'']
```

証明の1行目は仮説 ``h' : succ m = succ n`` をコンテキストに追加し、証明の2行目は仮説 ``h'' : m = n`` をコンテキストに追加する。

また、``injection`` タクティクは「異なるコンストラクタ(あるいは異なる入力を受けたコンストラクタ)の出力が互いに等しい」としたときに生じる矛盾を検出し、その矛盾を使ってゴールを閉じる。

```lean
open Nat

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  injection h

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  contradiction

example (h : 7 = 4) : False := by
  contradiction
```

2番目の例は、``contradiction`` タクティクもこの形の矛盾を検出することを示している。

## Inductive Families (帰納族)

Leanが受け入れる帰納的定義のほとんど全てを説明し終えた。ここまでの説明で、Leanでは任意個の再帰的コンストラクタを持つ帰納型を導入できることが分かった。実際、今までの知識を応用して、これから説明する方法を使うと、ただ1つの帰納的定義を使って帰納型の添字付き*family*(族)を導入することもできる。

帰納族とは、次のような形の1つの帰納的定義によって同時に定義される、添字を持つ型の族である:

```
inductive foo : ... → Sort u where
  | constructor₁ : ... → foo ...
  | constructor₂ : ... → foo ...
  ...
  | constructorₙ : ... → foo ...
```

ある ``Sort u`` の項を構築する通常の帰納的定義に対して、より一般的な帰納的定義は関数 ``... → Sort u`` を構築する。ここで、``...`` は*indices*(添字)とも呼ばれる引数の型の列を表す。そして、各コンストラクタは族のいくつかの要素を構築する。その一例が ``Vector α n`` の定義である。これは ``α`` の項を要素に持つ長さ ``n`` のベクトルの型である:

```lean
# namespace Hidden
inductive Vector (α : Type u) : Nat → Type u where
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# end Hidden
```

``cons`` コンストラクタは ``α`` と ``Vector α n`` の項を取り、``Vector α (n+1)`` の項を返す。これにより、族の1つの要素(型)の項を利用して別の要素(型)の項を構築することができる。

より風変わりな例は、Leanにおける等式型の定義である:

```lean
# namespace Hidden
inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a
# end Hidden
```

固定された各 ``α : Sort u`` と各 ``a : α`` に対して、この定義は ``x : α`` を添字とする型の族 ``Eq a x`` を構築する。しかし、注目すべきは、族 ``Eq a x`` には ``Eq a a`` の項を構築するただ1つのコンストラクタ ``refl`` しかないことである。直感的には、``Eq a x`` の証明を構築するには、``x`` が ``a`` である場合に反射律を使うしかないと言い換えることができる。``Eq a a`` は型の族 ``Eq a x`` の中で唯一の有項型であることに注意してほしい。

Leanにより生成された等号の除去則は次の通り:

```lean
universe u v

#check (@Eq.rec : {α : Sort u} → {a : α} → {motive : (x : α) → a = x → Sort v}
                  → motive a rfl → {b : α} → (h : a = b) → motive b h)
```

コンストラクタ ``refl`` とエリミネータ ``Eq.rec`` だけから等式の基本的な公理の全てが導かれるのは驚くべき事実である。ただし、節 [Axiomatic Details (公理の詳細)](#axiomatic-details-公理の詳細) で説明するように、等式の定義は非典型的である。

再帰子 ``Eq.rec`` は代入の定義にも使われる:

```lean
# namespace Hidden
theorem subst {α : Type u} {a b : α} {p : α → Prop} (h₁ : Eq a b) (h₂ : p a) : p b :=
  Eq.rec (motive := fun x _ => p x) h₂ h₁
# end Hidden
```

``match`` を使って ``subst`` を定義(証明)することもできる。 

```lean
# namespace Hidden
theorem subst {α : Type u} {a b : α} {p : α → Prop} (h₁ : Eq a b) (h₂ : p a) : p b :=
  match h₁ with
  | rfl => h₂
# end Hidden
```

実際、Leanは ``Eq.rec`` に基づいた定義を用いて ``match`` 式をコンパイルする。

```lean
# namespace Hidden
theorem subst {α : Type u} {a b : α} {p : α → Prop} (h₁ : Eq a b) (h₂ : p a) : p b :=
  match h₁ with
  | rfl => h₂

set_option pp.all true
#print subst
  -- ... subst.match_1 ...
#print subst.match_1
  -- ... Eq.casesOn ...
#print Eq.casesOn
  -- ... Eq.rec ...
# end Hidden
```

``h₁ : a = b`` に対して再帰子 ``Eq.rec`` または ``match`` を使うと、``a`` と ``b`` が同じだと仮定することができる。その下で、``p b`` と ``p a`` は同じである。

``Eq`` が対称的かつ推移的であることを証明するのは難しくない。以下の例では、等号の対称性 ``symm`` を示す。推移性 ``trans`` と*congruence*(合同性) ``congr`` の証明は練習問題として残す。

```lean
# namespace Hidden
theorem symm {α : Type u} {a b : α} (h : Eq a b) : Eq b a :=
  match h with
  | rfl => rfl

theorem trans {α : Type u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  sorry

theorem congr {α β : Type u} {a b : α} (f : α → β) (h : Eq a b) : Eq (f a) (f b) :=
  sorry
# end Hidden
```

型理論の研究においては、帰納的定義の更なる一般化が存在する。例えば、*induction-recursion* と *induction-induction* の原理がある。これらはLeanではサポートされていない。

## Axiomatic Details (公理の詳細)

これまで、例を通して帰納型とその構文について説明してきた。この節では、公理的な基礎に興味のある人のために、追加の情報を提供する。

帰納型のコンストラクタは、*parameters*(パラメータ, 帰納的な構築の間、固定されたままの引数)と*indices*(添字, 同時進行で構築される型の族をパラメータ化する引数)を取りうることを見てきた。各コンストラクタは、型を持つ必要がある。ここで、コンストラクタの引数の型は既に定義された型、パラメータと添字の型、現在定義中の帰納族の要素だけから構成される必要がある。コンストラクタの引数の型に現在定義中の帰納族の要素が現れる場合、それは*strictly positively*に出現しなければならないという要件がある。これは単純に、任意のコンストラクタの任意の引数の型は、定義中の帰納型が結果としてのみ出現する依存関数型でなければならないことを意味する。ここで、添字は定数と前の引数を使って与えられる。

帰納型はある ``u`` が存在して ``Sort u`` の項なので、当該帰納型を項としてみたとき、その項が持つ型宇宙として**どの**宇宙レベル ``u`` がふさわしいかを問うのは合理的である。帰納族 ``C`` の定義内の各コンストラクタ ``c`` は以下の形式をとる。

```
  c : (a : α) → (b : β[a]) → C a p[a,b]
```

ここで、``a`` はデータ型パラメータの列、``b`` はコンストラクタへの引数の列、``p[a, b]`` は添字である。この添字 ``p[a, b]`` によって、そのコンストラクタが帰納族のどの要素の項を構築するかが決まる。(この説明はやや不正確である。実際には、コンストラクタへの引数は、依存関係が意味をなす限りどのような順番で現れてもよい。)``C`` の宇宙レベルは、その帰納型が ``Prop``(つまり、``Sort 0``)に属するように指定されているかどうかによって、2種類の制約を持つ。

まず、帰納型が ``Prop`` に属するように指定されて**いない**場合を考えよう。このとき、宇宙レベル ``u`` は次を満たすように制約される:

> 上記の各コンストラクタ ``c`` と、列 ``β[a]`` 内の各 ``βk[a]`` に対して、もし ``βk[a] : Sort v`` なら、``u`` ≥ ``v`` である。

言い換えれば、当該帰納型の宇宙レベル ``u`` は、各コンストラクタの各引数の型の宇宙レベル以上であることが要求される。

帰納型が ``Prop`` に属するように指定されている場合、コンストラクタの引数の型の宇宙レベルには制約がない。しかし、コンストラクタの引数の型の宇宙レベルは除去則に影響を与える。一般的に、``Prop`` に属する帰納型の場合、除去則のmotive(動機)の型は ``Prop`` に属することが要求される。

この最後のルールには例外がある: コンストラクタが1つしかなく、コンストラクタの各引数が ``Prop`` の項あるいは添字である場合、除去則によって帰納的に定義された ``Prop`` を除去して任意の ``Sort`` の項を作ることが許される。この場合、直感的には、エリミネータは引数の型が有項であるという事実なしに引数の情報を利用することはない、と言うことができる。この特別なケースは*singleton elimination*(シングルトン除去)として知られている。

帰納的に定義された等式型のエリミネータ ``Eq.rec`` の実用例で、シングルトン除去が活躍するのをすでに見てきた。``p a`` と ``p b`` が ``Prop`` に限らない任意の型を持つ場合でも、項 ``h : Eq a b`` を使って項 ``t' : p a`` を ``p b`` にキャストすることができる。なぜなら、このキャストは新しいデータを生成せず、すでに持っているデータを再解釈するだけだからだ。シングルトン除去はheterogeneous equality(異型等式)やwell-founded recursion(整礎再帰)でも使われるが、これについては次章の[Well-Founded Recursion and Induction (整礎再帰と整礎帰納法)](./induction_and_recursion.md#well-founded-recursion-and-induction-整礎再帰と整礎帰納法)の節で説明する。

## Mutual and Nested Inductive Types (相互帰納型と入れ子帰納型)

ここで、帰納型を一般化して得られるしばしば便利な2つの型の概念*Mutual Inductive Types*(相互帰納型)と*Nested Inductive Types*(入れ子帰納型)について考えよう。Leanは、これらを上で説明したようなよりプリミティブな種類の帰納型に「コンパイル」することでこの2つの概念をサポートする。言い換えると、Leanはより一般的な定義を構文解析し、それに基づいて補助的な帰納型を定義し、その補助的な型を使って本当に必要なものを定義する。これらの型を効果的に利用するためには、次の章で説明するLeanの等式コンパイラが必要である。それでも、これらの型の宣言は通常の帰納的定義の簡単な変化形であるため、ここで説明することに意味がある。

まず、Leanは*mutually defined*(相互に定義された)帰納型をサポートする。これは、同時に定義される、それぞれが定義中の他の型を参照する帰納型たちである。

```lean
mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : (n : Nat) → Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : (n : Nat) → Even n → Odd (n + 1)
end

open Even Odd

example : Even 2 := even_succ 1 (odd_succ 0 even_zero)
```

この例では、2つの帰納型が同時に定義されている: 自然数 ``n`` は、``0`` であるか奇数 ``Odd`` より1大きいときは偶数 ``Even`` であり、偶数 ``Even`` より1大きいときは奇数 ``Odd`` である。以下の練習問題では、その詳細を記述せよ。

相互帰納型は、``α`` の項でラベル付けされた頂点を持つ有限木を定義するのにも使える:

```lean
mutual
    inductive Tree (α : Type u) where
      | node : α → TreeList α → Tree α

    inductive TreeList (α : Type u) where
      | nil  : TreeList α
      | cons : Tree α → TreeList α → TreeList α
end
```

この定義により、``α`` の項 ``a`` と、空であってもよい部分木のリストを与えることで、``a`` を根とする ``Tree α`` の項を構築することができる。部分木のリストは型 ``TreeList α`` の項として表現され、これは空リスト ``nil`` か、``Tree α`` の項と ``TreeList α`` の項の ``cons`` のいずれかであると定義される。

しかしながら、この ``Tree`` と ``TreeList`` の定義は扱いにくい。特にLeanのライブラリにはリストを扱うための関数や定理が数多く含まれているため、部分木のリストが型 ``List (Tree α)`` の項として与えられたら、これらの定義はもっと扱いやすくなるだろう。型 ``TreeList α`` が ``List (Tree α)`` と「同型」であることを示すことはできる。しかし、この同型に沿って片方で得られた結果を他方へ翻訳するのは面倒である。

実際、Leanでは本当に必要としている帰納型を定義することができる:

```lean
inductive Tree (α : Type u) where
  | mk : α → List (Tree α) → Tree α
```

これは*nested inductive type*(入れ子帰納型)として知られている。この ``Tree`` の定義は前節で示した帰納型の厳密な仕様から外れている。なぜなら、``mk`` の引数の型の中で、``Tree`` はstrictly positivelyに現れず、``List`` 型コンストラクタの中に入れ子になっているからである。Leanはカーネルの中で ``TreeList α`` と ``List (Tree α)`` の間に同型を構築し、その同型の観点からこの入れ子帰納型 ``Tree`` のコンストラクタを定義する。

## Exercises (練習問題)

1. 自然数に対する他の演算、例えば乗法、前者関数(``pred 0 = 0`` とする)、切り捨て減法(``m`` が ``n``以上のとき ``n - m = 0``)、べき乗などを定義してみよ。次に、既に証明した定理を基に、それらの基本的な性質をいくつか証明してみよ。

   それらの多くはLeanのコアライブラリで既に定義されている。名前衝突を避けるため、``Hidden`` のような名前の名前空間の中で作業することを勧める。

2. リストに関する ``length`` 関数や ``reverse`` 関数のような操作をいくつか定義せよ。それらについて、次のような性質をいくつか証明せよ。

   a. ``length (s ++ t) = length s + length t``

   b. ``length (reverse t) = length t``

   c. ``reverse (reverse t) = t``

3. 以下のコンストラクタから構築される項からなる帰納データ型を定義せよ:

   - ``const n``, 自然数 ``n`` を表す定数
   - ``var n``, ``n`` 番目の変数
   - ``plus s t``, ``s`` と ``t`` の和を表す
   - ``times s t``, ``s`` と ``t`` の積を表す

   今定義した型の項を評価する関数を再帰的に定義せよ。ただし、変数には値を割り当てることができるとする。

4. 同様に、命題論理式の型と、その型に関する関数を定義せよ:
   例えば、評価関数、式の複雑さを測る関数、与えられた変数に別の式を代入する関数などを定義せよ。
