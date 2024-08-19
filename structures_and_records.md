# Structures and Records (構造体とレコード)

Leanの基礎システムは帰納型を含むことを見てきた。さらに、型宇宙、依存関数型、そして帰納型のみで巨大で頑丈な数学の体系を構築できるという驚くべき事実を説明した。それ以外の全てはこの3種類の型から派生するのである。Leanの標準ライブラリには帰納型の具体例(例えば ``Nat``、``Prod``、``List``)が多数含まれており、論理的結合子でさえも帰納型を用いて定義されている。

コンストラクタを1つだけ持つ非再帰的帰納型は*structure*(構造体)または*record*(レコード)と呼ばれることを思い出してほしい。直積型は構造体であり、依存直積型(シグマ型)も同様に構造体である。一般に、構造体 ``S`` が定義されるとき、``S`` の各インスタンス(レコード or オブジェクト)を「分解」し、そのフィールドに格納されている値を取り出すことができる*projection*(射影)関数も同時に定義することが多い。直積ペアの1番目の要素を返す関数 ``prod.fst`` と2番目の要素を返す関数 ``prod.snd`` はそのような射影関数の例である。

プログラムを書いたり数学を形式化するとき、多くのフィールドを含む構造を定義することは珍しくない。Leanでは、``structure`` コマンドが構造体の定義をサポートするインフラを提供する。このコマンドを使って構造体を定義すると、Leanは各フィールドに対する射影関数を自動生成する。``structure`` コマンドは、以前に定義した構造体に基づいて新しい構造体を定義することもできる。さらに、Leanは与えられた構造体のインスタンスを定義するための便利な記法も提供する。

## Declaring Structures (構造体を定義する)

``structure`` コマンドは、言わば帰納データ型を定義するための「フロントエンド」である。全ての ``structure`` 宣言は、構造体に与えられた名前と同じ名前の名前空間を導入する。``structure`` コマンドの構文の一般的な形式は次の通りである:

```
    structure <name> <parameters> <parent-structures> where
      <constructor> :: <fields>
```

ほとんどの部分はオプションである。構造体定義の例を挙げる:

```lean
structure Point (α : Type u) where
  mk :: (x : α) (y : α)
```

``Point`` 型の値はコンストラクタ ``Point.mk a b`` を使って生成され、点 ``p`` のフィールドには ``Point.x p`` と ``Point.y p`` を使ってアクセスする(以下で見るように、``p.x`` と ``p.y`` も同様に機能する)。``structure`` コマンドは定義した構造体に関する有用な再帰子や定理も自動生成する。上の ``Point`` 型の宣言の際に自動生成されたもののいくつかを以下に挙げる。

```lean
# structure Point (α : Type u) where
#  mk :: (x : α) (y : α)
#check Point       -- a Type
#check @Point.rec  -- the eliminator
#check @Point.mk   -- the constructor
#check @Point.x    -- a projection
#check @Point.y    -- a projection
```

コンストラクタ名を指定しなかった場合、デフォルトでコンストラクタは ``mk`` と名付けられる。また、各フィールドの間に改行を入れると、フィールド名を括弧で囲むのを省略することができる。

```lean
structure Point (α : Type u) where
  x : α
  y : α
```

``structure`` コマンドにより自動生成されたものを使った簡単な定理や式をいくつか紹介しよう。いつものように、``open Point`` コマンドを使えば ``Point`` という接頭辞を省略した名前を使えるようになる。

```lean
# structure Point (α : Type u) where
#  x : α
#  y : α
#eval Point.x (Point.mk 10 20)
#eval Point.y (Point.mk 10 20)

open Point

example (a b : α) : x (mk a b) = a :=
  rfl

example (a b : α) : y (mk a b) = b :=
  rfl
```

``p : Point Nat`` が与えられたとき、ドット記法 ``p.x`` は ``Point.x p`` の略記である。これは構造体のフィールドにアクセスする便利な方法である。

```lean
# structure Point (α : Type u) where
#  x : α
#  y : α
def p := Point.mk 10 20

#check p.x  -- Nat
#eval p.x   -- 10
#eval p.y   -- 20
```

ドット記法はレコードの射影関数にアクセスするときだけでなく、同じ名前空間内で定義された他の関数を適用するときにも便利である。節[Conjunction (連言)](./propositions_and_proofs.md#conjunction-連言)の内容を思い出してほしい。``p`` が ``Point`` 型を持ち、``foo`` の最初の非暗黙引数が ``Point`` 型を持つなら、式 ``p.foo`` は ``Point.foo p`` と解釈される。したがって、次の例のように、式 ``p.add q`` は ``Point.add p q`` の略記となる。

```lean
structure Point (α : Type u) where
  x : α
  y : α
  deriving Repr

def Point.add (p q : Point Nat) :=
  mk (p.x + q.x) (p.y + q.y)

def p : Point Nat := Point.mk 1 2
def q : Point Nat := Point.mk 3 4

#eval p.add q  -- {x := 4, y := 6}
```

次の章では、型 ``α`` に関連する加法演算があるという仮定の下、``add`` のような関数を定義して、それが ``Point Nat`` だけでなく ``Point α`` の項に対して汎用的に機能するようにする方法を学ぶ。

より一般的には、項 ``p : Point`` と式 ``p.foo x y z`` が与えられると、Leanは ``Point.foo`` の「``Point`` 型の」最初の引数として ``p`` を挿入する。例えば、以下のスカラー倍の定義では、``p.smul 3`` は ``Point.smul 3 p`` と解釈される。

```lean
# structure Point (α : Type u) where
#  x : α
#  y : α
#  deriving Repr
def Point.smul (n : Nat) (p : Point Nat) :=
  Point.mk (n * p.x) (n * p.y)

def p : Point Nat := Point.mk 1 2

#eval p.smul 3  -- {x := 3, y := 6}
```

``List.map`` 関数では同様のトリックがよく使われる。``List.map`` 関数は2番目の非暗黙引数としてリストを取る:

```lean
#check @List.map

def xs : List Nat := [1, 2, 3]
def f : Nat → Nat := fun x => x * x

#eval xs.map f  -- [1, 4, 9]
```

ここで、``xs.map f`` は ``List.map f xs`` と解釈されている。

## Objects (オブジェクト)

これまでコンストラクタを使って構造体の項を作成してきた。多くのフィールドを含む構造体の場合、コンストラクタを使って構造体の項を作成する方法は、フィールドが定義された順番を覚えておく必要があるため、しばしば不便である。そこで、Leanでは構造体の項を定義するための次のような代替記法を用意している。(訳者注: ``*`` は括弧内が1回以上の繰り返しからなることを表す。実際にこの構文を用いるときに括弧を書く必要はない。)

```
    { (<field-name> := <expr>)* : structure-type }
    or
    { (<field-name> := <expr>)* }
```

接尾辞 ``: structure-type`` は、期待される構造体の型が与えられた情報から推論できる場合はいつでも省略できる。例えば、``Point`` 型のオブジェクト「点」を定義するためにこの記法を用いる。フィールドを指定する順番は任意であるため、以下の式は全て同じ点を定義する。

```lean
structure Point (α : Type u) where
  x : α
  y : α

#check { x := 10, y := 20 : Point Nat }    -- { (<field-name> := <expr>)* : structure-type }
#check { y := 20, x := 10 : Point _ }      -- フィールドを指定する順番は任意
#check ({ x := 10, y := 20 } : Point Nat)  -- { (<field-name> := <expr>)* } 構造体の型が明らか

example : Point Nat :=
  { y := 20, x := 10 }                     -- { (<field-name> := <expr>)* } 構造体の型が明らか
```

フィールドの値が指定されていない場合、Leanはその値を推論しようとする。指定されていないフィールドの値を推論できなかった場合、Leanは対応するプレースホルダーを埋められなかったことを示すエラーフラグを立てる。

```lean
structure MyStruct where
    {α : Type u}
    {β : Type v}
    a : α
    b : β

#check { a := 10, b := true : MyStruct }
```

*Record update*(レコード更新)は、古いレコード(オブジェクト)の1つまたは複数のフィールドの値を変更して新しいレコードを作成する、もう1つの一般的操作である。Leanでは、フィールドへの値の割り当ての前に ``s with`` という注釈を追加することで、新しいレコード内の値未割り当てのフィールドを古いレコード ``s`` から取得するように指示することができる。複数の古いレコードが提供された場合、新しいレコード内でまだ値が指定されていないフィールドを含むレコードを見つけるまで、Leanは提供されたレコードを順番に参照する。全てのオブジェクトを参照した後、新しいレコード内に値未指定のフィールドが存在した場合、Leanはエラーを発生させる。

```lean
structure Point (α : Type u) where
  x : α
  y : α
  deriving Repr

def p : Point Nat :=
  { x := 1, y := 2 }

#eval { p with y := 3 }  -- { x := 1, y := 3 }
#eval { p with x := 4 }  -- { x := 4, y := 2 }

structure Point3 (α : Type u) where
  x : α
  y : α
  z : α

def q : Point3 Nat :=
  { x := 5, y := 5, z := 5 }

def r : Point3 Nat :=
  { p, q with x := 6 }

example : r.x = 6 := rfl
example : r.y = 2 := rfl
example : r.z = 5 := rfl
```

## Inheritance (継承)

新しいフィールドを追加することで、既存の構造体を*extend*(拡張)させることができる。この機能によって、一種の*inheritance*(継承)をシミュレートすることができる。

```lean
structure Point (α : Type u) where
  x : α
  y : α

inductive Color where
  | red | green | blue

structure ColorPoint (α : Type u) extends Point α where
  c : Color
```

次の例では、多重継承(複数の親構造体を一度に継承すること)を使って新しい構造体 ``RedGreenPoint`` を定義し、各親構造体のオブジェクトを使って ``RedGreenPoint`` 型のオブジェクトを定義する。

```lean
structure Point (α : Type u) where
  x : α
  y : α
  z : α

structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat

structure RedGreenPoint (α : Type u) extends Point α, RGBValue where
  no_blue : blue = 0

def p : Point Nat :=
  { x := 10, y := 10, z := 20 }

def rgp : RedGreenPoint Nat :=
  { p with red := 200, green := 40, blue := 0, no_blue := rfl }

example : rgp.x   = 10 := rfl
example : rgp.red = 200 := rfl
```
