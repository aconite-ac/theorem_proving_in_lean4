# Dependent Type Theory (依存型理論)

Dependent Type Theory(依存型理論)は強力で表現力の高い言語であり、複雑な数学的主張を表現したり、複雑なハードウェアやソフトウェアの仕様を記述したり、これら両方について自然で統一された方法で推論したりすることができる。Leanは*Calculus of Constructions*として知られる依存型理論の一種に基づいている。そして、Leanは「非累積的宇宙の可算無限階層」と「帰納型」を備えている。この章が終わるころには、これらが意味するところを理解できているだろう。

## Simple Type Theory (単純型理論)

「型理論」という名前は「全てのexpression(式 あるいは 項)はそれに関連した型を持つ」という事実に由来する。例えば、適切な文脈の下で項 ``x + 0`` は自然数型を持ち、項 ``f`` は自然数を受け取り自然数を返す関数型を持つ。正確な定義を述べると、Leanにおいて「自然数」とは「任意精度の符号なし整数」のことである。

Leanでは項を次のように宣言する。

```lean
-- def <項の名前(識別子)> : <項の型> := <項の定義式>
def m : Nat := 1           -- `m` は自然数型を持つ
def b1 : Bool := true      -- `b1` はブール型を持つ
def b2 : Bool := false
```

項の型をチェックするには次のようにする。

```lean
# def m : Nat := 1
# def b1 : Bool := true
# def b2 : Bool := false
-- #check <項>
#check m                   -- output: Nat
#check b1 && b2            -- `&&` は「かつ」 output: Bool
#check b1 || b2            -- `||` は「または」 output: Bool
```

項を評価する(項の値を計算する)には次のようにする。

```lean
# def m : Nat := 1
# def b1 : Bool := true
# def b2 : Bool := false
-- #eval <項>
#eval 5 * 4                -- 20
#eval m + 2                -- 3
#eval b1 && b2             -- false
```

``/-`` と ``-/`` はコメントブロックを形成し、その中のテキストは無視される。同様に、``--`` から行末までもコメントとみなされ、コメントは無視される。コメントブロックは入れ子にすることができる。そのため、多くのプログラミング言語と同じように、コードの塊を「コメントアウト」することができる。

``def`` キーワードは現在の作業環境で新しい名前付きの項を宣言(定義)する。上の例では、``def m : Nat := 1`` は値が ``1`` である ``Nat`` 型の新しい項 ``m`` を定義している。``#check <項の名前>`` コマンドはその項が持つ型を報告するようLeanに要求する。Leanでは、システムに情報を問い合わせる補助コマンドは基本的にハッシュ記号(``#``)から始まる。``#eval <項の名前>`` コマンドはその項を評価するようLeanに要求する。いくつかの項を自分で宣言し、いくつかの項を自分で型チェックしてみてほしい。``def`` を使って新しいオブジェクトを宣言することは、システム上で実験するための良い方法である。

Simple Type Theory(単純型理論)が強力なのは、他の型から新しい型を作ることができるからである。例えば、``a`` と ``b`` が型なら、``a -> b`` は ``a`` から ``b`` への関数の型を表し、``a × b`` は ``a`` の要素と ``b`` の要素からなるペアの型(``a`` と ``b`` の直積型)を表す。ここで、``×`` はUnicode記号であることに注意してほしい。LeanではUnicodeを使用する。Unicodeを適切に使用することで読みやすさを向上させることができる。また、全ての現代的なエディタはUnicodeをサポートしている。Leanの標準ライブラリでは、型を表すギリシャ文字や、``->`` をよりコンパクトにしたUnicode記号 ``→`` をよく見かける。

``→`` や ``×`` などを使った例を掲載する。

```lean
#check Nat → Nat                   -- `→` は "\to" あるいは "\r" と打つと入力できる
#check Nat -> Nat                  -- `->` は `→` のASCII表記

#check Nat × Nat                   -- `×` は "\times" と打つと入力できる
#check Prod Nat Nat                -- `Prod Nat Nat` は `Nat × Nat` のASCII表記

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)           -- これは1つ上と同じである。つまり、`→` は右結合的である
#check Nat × Nat → Nat
#check (Nat → Nat) → Nat           -- 関数を受け取る関数の型

#check Nat.succ                    -- Nat → Nat
#check (0, 1)                      -- Nat × Nat
#check Nat.add                     -- Nat → Nat → Nat

#check Nat.succ 2                  -- Nat
#check Nat.add 3                   -- Nat → Nat
#check Nat.add 5 2                 -- Nat
#check (5, 9).1                    -- Nat
#check (5, 9).2                    -- Nat

#eval Nat.succ 2                   -- 3
#eval Nat.add 5 2                  -- 7
#eval (5, 9).1                     -- 5
#eval (5, 9).2                     -- 9
#eval Nat.add (10, 7).1 (10, 7).2  -- 17
```

今一度、自分でいくつかの例を作り、これらのコマンドを試してほしい。

基本的な構文を見てみよう。Unicodeの矢印 ``→`` は ``\to``、``\r``、``\->`` と打つことで入力できる。ASCIIの代替記号 ``->`` も使用できる。したがって、``Nat -> Nat`` と ``Nat → Nat`` は同じ意味である。どちらの式も、入力として自然数を受け取り、出力として自然数を返す関数の型を表す。直積型を表すUnicode記号 ``×`` は ``\times`` と打つと入力できる。一般に、``α``、``β``、``γ`` のような小文字のギリシャ文字を使って型を表す。これらは ``\a``、``\b``、``\c`` と打つと入力できる。

以下に上述した記号の入力方法をまとめる。

| 入力     | 記号     |
|:--------:|:-------:|
| \to      | →       |
| \r       | →       |
| \->      | →       |
| \times   | ×       |
| \a       | α       |
| \b       | β       |
| \g       | γ       |

上記の例について注意すべきことがさらにいくつかある。まず、項 ``x`` に対する関数 ``f`` の適用は ``f x`` と表記される(例: ``Nat.succ 2``)。次に、型の記述において ``→`` は右結合的である。例えば、``Nat.add`` の型は ``Nat → Nat → Nat`` であり、これは ``Nat → (Nat → Nat)`` と等価である。したがって、``Nat.add`` を、自然数を受け取り「自然数を受け取り自然数を返す関数」を返す関数とみなすことができる。型理論においては、``Nat.add`` を自然数のペアを入力として受け取り、自然数を出力として返す関数として表現するよりも、一般的にこちらの方が便利である。つまり、``Nat.add`` の型を ``Nat × Nat → Nat`` とするよりも、``Nat → Nat → Nat`` とする方が便利である。これにより、例えば ``Nat.add`` 関数を「部分適用」することができる。上記の例は ``Nat.add 3`` は ``Nat → Nat`` 型を持つことを示している。すなわち、``Nat.add 3`` は2番目の引数 ``n`` を「待つ」関数を返す。したがって、``Nat.add 3`` は ``Nat.add 3 n`` と書くのと等価である。

``m : Nat`` と ``n : Nat`` があれば、``(m, n)`` は ``Nat × Nat`` 型を持つ ``m`` と ``n`` の順序対を表すことが分かっただろう。この記法は自然数のペアを作る方法を与えてくれる。逆に、``p : Nat × Nat`` とすると、``p.1 : Nat``、``p.2 : Nat`` となる。この記法を使うとペアの2つの成分を取り出すことができる。

## Types as objects (項としての型)

型そのもの(``Nat`` や ``Bool`` など)も項であるとみなすことは、Leanの依存型理論が単純型理論を拡張するのに使う手法の1つである。そうみなすためには、``Nat`` や ``Bool`` などの各型も型を持っていなければならない。

```lean
#check Nat               -- Type
#check Bool              -- Type
#check Nat → Bool        -- Type
#check Nat × Bool        -- Type
#check Nat → Nat         -- ...
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat
```

上の各式が ``Type`` 型の項であることがわかるだろう。型を表す新しい定数を宣言することもできる:

```lean
def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α        -- Type
#check F α      -- Type
#check F Nat    -- Type
#check G α      -- Type → Type
#check G α β    -- Type
#check G α Nat  -- Type
```

上の例が示すように、``Type → Type → Type`` 型を持つ関数の例、すなわち直積 ``Prod`` はすでに見た:

```lean
def α : Type := Nat
def β : Type := Bool

#check Prod α β       -- Type
#check α × β          -- Type

#check Prod Nat Nat   -- Type
#check Nat × Nat      -- Type
```

任意の型 ``α`` が与えられたとき、型 ``List α`` は型 ``α`` の項からなるリストの型を表す。

```lean
def α : Type := Nat

#check List α    -- Type
#check List Nat  -- Type
```

Leanの全ての式(項)が型を持っていることを考えれば、「``Type`` そのものはどのような型を持っているのか」と問うのは自然なことである。

```lean
#check Type      -- Type 1
```

では ``Type 1`` の型を予想し、それから実際に ``Type 1`` の型をチェックしてみよう。

```lean
#check Type 1
#check Type 2
#check Type 3
#check Type 4
```

予想は当たっただろうか。この実験において、我々は「Leanは型の無限階層の上に成り立っている」というLeanの型付けシステムの最も精緻な側面の一つに突き当たっている。

``Type 0`` は ``Nat`` のような「小さい」あるいは「普通の」型たちからなる宇宙だと思ってほしい。``Type 1`` は ``Type 0`` を項にもつより大きい宇宙であり、``Type 2`` は ``Type 1`` を項にもつより大きい宇宙である。この列に限りはない。つまり、任意の自然数 ``n`` に対して、型 ``Type n`` が存在する。``Type`` とは ``Type 0`` の略称である:

```lean
#check Type
#check Type 0
```

次の表は、今議論されていることを理解するのに役立つだろう。右方向に進むと「宇宙」がより大きいものへと変化し、下方向に進むと「度」と呼ばれるものが変化する。

|           |               |               |                 |                        |     |
|:---------:|:-------------:|:-------------:|:---------------:|:----------------------:|:---:|
| sort      | Prop (Sort 0) | Type (Sort 1) | Type 1 (Sort 2) | Type 2 (Sort 3)        | ... |
| type(型)  | True          | Bool          |   Nat -> Type   | Type -> Type 1         | ... |
| term(項)  | trivial       | true          | fun n => Fin n  | fun (_ : Type) => Type | ... |

いくつかの演算子は型の宇宙に対して*polymorphic*(多相)である必要がある。例えば、``List α`` は、``α`` がどの型宇宙にいようと意味をなすべきである。多相な関数 ``List`` の型は次のように表記される:

```lean
#check List    -- List.{u} (α : Type u) : Type u
```

ここで、``u`` は宇宙レベルを表す変数である。コマンド ``#check List`` の出力は、``α`` が型 ``Type n`` を持つなら、``List α`` も ``Type n`` を持つことを表している。関数 ``Prod`` も多相である:

```lean
#check Prod    -- Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)
```

``universe`` コマンドを使うと、明示的に宇宙変数を宣言することができる。宇宙変数を使うと多相な項を定義することができる:

```lean
universe u
def F (α : Type u) : Type u := Prod α α       -- `Type u` に属する型 `α` を受け取ると、`α` と `α` の直積型を返す関数
#check F                                      -- Type u → Type u
```

次のように ``{}`` を用いて宇宙パラメータを指定することもできる。そうすれば ``universe`` コマンドの使用を回避できる。

```lean
def F.{u} (α : Type u) : Type u := Prod α α

#check F    -- Type u → Type u
```

## Function Abstraction and Evaluation (関数抽象と評価)

Leanでは、キーワード ``fun`` (あるいは ``λ``) を使うと、式から関数を作ることができる。

```lean
-- 括弧は省略可能
-- fun (<入力引数の名前> : <入力引数の型名>) => <関数の出力を定義する式>
-- λ (<入力引数の名前> : <入力引数の型名>) => <関数の出力を定義する式>
#check fun (x : Nat) => x + 5   -- Nat → Nat
#check λ (x : Nat) => x + 5     -- `λ` と `fun` は同じ意味
#check fun x => x + 5           -- `x` は `Nat` 型だと推論される
#check λ x => x + 5             -- `x` は `Nat` 型だと推論される
```

要求されたパラメータを通すことにより、ラムダ関数を評価することができる。

```lean
#eval (λ x : Nat => x + 5) 10    -- 15
```

もし入力引数 ``x : α`` があり、さらに式 ``t : β`` が作れるなら、式 ``fun (x : α) => t`` (``λ (x : α) => t``) は型 ``α → β`` を持つ。このように、「入力引数」と「出力を定義する式」を結びつけて新しい関数を作るプロセスは*lambda abstraction*(ラムダ抽象)として知られている。``fun (x : α) => t`` は型 ``α`` から型 ``β`` への、任意の値 ``x`` を値 ``t`` に写す関数だと考えてほしい。

他のいくつかの例を挙げる:

```lean
#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2   -- Nat → Bool → Nat
```

Leanはこの3つの例を全く同じ式であると解釈する。最後の例では、入力の型が省略されているにも関わらず、``#check`` コマンドは期待した型を返してくれている。これはLeanが式 ``if not y then x + 1 else x + 2`` から入力の型を推論したからである。

関数の操作の数学的に一般的な例は、ラムダ抽象を用いて記述することができる:

```lean
def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x        -- Nat → Nat
#check fun x : Nat => true     -- Nat → Bool
#check fun x : Nat => g (f x)  -- Nat → Bool
#check fun x => g (f x)        -- Nat → Bool
```

これらの式の意味を考えてみよう。式 ``fun x : Nat => x`` は ``Nat`` 上の恒等関数を表す。式 ``fun x : Nat => true`` は常に ``true`` を返す定数関数を表す。式 ``fun x : Nat => g (f x)`` は ``f`` と ``g`` の合成を表す。一般的に、入力引数の型注釈を省略して、Leanに型を推論してもらうことができる。例えば、``fun x : Nat => g (f x)`` の代わりに ``fun x => g (f x)`` と書くことができる。

入力引数として関数を与えることもできる:

```lean
#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)
-- (String → Bool) → (Nat → String) → Nat → Bool
```

何なら型を入力引数として与えることもできる:

```lean
#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)
```

例えば、最後の式は3つの型 ``α``、``β``、``γ`` と2つの関数 ``g : β → γ`` と ``f : α → β`` を受け取り、``g`` と ``f`` の合成を返す。(この関数の型が意味をなすようにするには「依存積」の概念が必要になるが、それは後ほど説明される。)

ラムダ抽象の一般的な形式は ``fun x : α => t`` である。ここで、変数 ``x`` は*bounded variable*(束縛変数)と呼ばれる: この ``x`` は実際単なるプレースホルダーであり、その「スコープ」は式 ``t`` の中に限定され、``t`` を超えて広く及ぶことはない。例えば、定数 ``b`` が既に宣言されていたとする。この後に項 ``fun (b : β) (x : α) => b`` を作ったとしても、その中の ``b`` は既存の定数 ``b`` には影響しない。ラムダ抽象内の束縛変数名はどのように変えてもいい。実際、項 ``fun (b : β) (x : α) => b`` と項 ``fun (u : β) (z : α) => u`` は全く同じ関数である。

束縛変数の名前を変えることで互いに同じだと分かる式たちのことを*alpha equivalent*(α-同値)と呼ぶ。そして、α-同値なものは「同じ」だとみなされる。Leanはα-同値を認識している。

項 ``t : α → β`` を 項 ``s : α`` に適用すると、項 ``t s : β`` が得られることに注意してほしい。型を入力として受け取るようにし、分かりやすさのため束縛変数をリネームすると、以前の例は次のように書き換えられる:

```lean
#check (fun x : Nat => x) 1     -- Nat
#check (fun x : Nat => true) 1  -- Bool

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check
  (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool g f 0
  -- Bool
```

期待通り、式 ``(fun x : Nat => x) 1`` は ``Nat`` 型を持つ。もっと詳しいことが言える: ``1`` に式 ``(fun x : Nat => x)`` を適用したら、値 ``1`` が出力されるべきである。そして、実際にそうである:

```lean
def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#eval (fun x : Nat => x) 1     -- 1
#eval (fun x : Nat => true) 1  -- true
#eval (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool g f 0  -- true
```

これらの項がどのように評価されているのかは後ほど学ぶ。今のところ、次の依存型理論の重要な特徴に注目してほしい: 全ての項が計算上の動作を持ち、またnormalization(正規化)の概念をサポートしている。原則として、同じ値に簡約される2つの項は*definitionally equal*であると呼ばれる。Leanの型チェッカーはdefinitionally equalである2つの項を「同じ」とみなす。Leanは2つの項の間の相等関係を認識しサポートするために最善を尽くす。

Leanは完全なプログラミング言語である。バイナリ実行ファイルを生成するコンパイラと、対話型のインタプリタがある。コマンド ``#eval`` で式を評価することができ、``#eval`` は関数をテストする方法として好まれている。

## Definitions (定義)

``def`` キーワードは名前付きの新しい項を宣言する重要な方法を提供することを思い出してほしい。

```lean
-- def <関数の名前> (<入力引数の名前> : <入力引数の型>) : <出力の型> := <出力を定義する式>

def double (x : Nat) : Nat :=
  x + x
```

他のプログラミング言語における関数の働きを知っていると、この定義の仕方がより馴染み深くなるかもしれない。``double`` は ``Nat`` 型の入力パラメータ ``x`` を取り、呼び出すと ``x + x`` を出力する関数である。したがって、出力の型は ``Nat`` 型である。この関数は次のように使うことができる:

```lean
# def double (x : Nat) : Nat :=
#  x + x
#eval double 3    -- 6
```

``def`` を名前付きのラムダ抽象だと考えることもできる。次の例は直前の例と同じ結果を得る:

```lean
def double : Nat → Nat :=
  fun x => x + x

#eval double 3    -- 6
```

型を推論するのに十分な情報があるなら、型宣言を省略することができる。型推論はLeanの重要な部分である:

```lean
def double :=
  fun (x : Nat) => x + x
#eval double 3    -- 6
```

改めて、定義に用いる一般的な文法は次のように書ける。

```
def foo : α := bar
```

ここで ``α`` は式 ``bar`` により定義される出力の型である。Leanは通常、型 ``α`` が何であるかを推論できるため、``α`` を省略しても問題ないことが多い。しかし、``α`` を明示的に書くことはしばしば良いことである。型の明示は書き手の意図を明確にする。そして、Leanは ``bar`` が持つ型と ``α`` が一致するかをチェックしてくれる。もし一致しなければ、Leanはエラーを返す。

右辺 ``bar`` はラムダ式に限らずどんな式でもよい。したがって、``def`` は次のように単に値に名前を付けるために使ってもよい:

```lean
def pi := 3.141592654
```

``def`` は複数の入力パラメータを受け取ることができる。2つの自然数を足し合わせる関数を作ってみよう:

```lean
def add (x y : Nat) :=
  x + y

#eval add 3 2               -- 5
```

パラメータリストは2つ以上に分けて書くこともできる:

```lean
# def double (x : Nat) : Nat :=
#  x + x
def add (x : Nat) (y : Nat) :=
  x + y

#eval add (double 3) (7 + 9)  -- 22
```

最後の行では、``add`` への第1引数を作るために ``double`` 関数を呼び出したことに注意してほしい。

``def`` の中では他の面白い式を使うこともできる:

```lean
def greater (x y : Nat) :=
  if x > y then x
  else y

#eval greater 7 6             -- 7
#eval greater 99 100          -- 100
#eval greater 5 5             -- 5
```

``greater`` 関数がどんな働きをするかはおそらく推測できるだろう。

入力として他の関数を受け取る関数を定義することもできる。次の定義 ``doTwice`` は第1引数として与えられた関数 ``f`` を2回呼び出し、``f`` に第2引数 ``x`` を入力して得られた出力を再び ``f`` に入力し、そこから得られた出力を返す:

```lean
def double :=
  fun (x : Nat) => x + x

def square :=
  fun (x : Nat) => x * x

def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

#eval doTwice double 2        -- 8
#eval doTwice square 3        -- 81
```

少し抽象的な例を見てみよう。次のように型を入力引数として指定することができる:

```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

``compose`` は入力引数として任意の2つの関数 ``g``、``f`` を受け取る。ただし、``g`` と ``f`` はともにただ1つの入力を受け取る関数でなければならない。さらに ``g : β → γ`` と ``f : α → β`` は、``f`` の出力の型と ``g`` の入力の型が一致していなければならないという制約を意味する。``g`` と ``f`` が以上の制約を満たすなら、``compose`` は意味をなす。そうでなければ2つの関数は合成不可能である。

``compose`` は型 ``α`` を持つ第3引数 ``x`` をとる。``x`` は ``f`` に入力され、``f`` からの出力は ``g`` に入力される。``g`` は型 ``γ`` の項を返す。したがって、``compose`` 関数の返り値の型も ``γ`` である。

``compose`` は任意の型 ``α β γ`` について機能するという意味で非常に普遍的である。これは任意の2つの関数 ``g f`` がともにただ1つの入力を受け取り、``f`` の出力の型と ``g`` の入力の型が一致しているならば、``compose`` は ``g`` と ``f`` を合成できることを意味する。以下に例を挙げる:

```lean
def double :=
  fun (x : Nat) => x + x

def square :=
  fun (x : Nat) => x * x

def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

#eval compose Nat Nat Nat double square 3        -- 18
#eval compose Nat Nat Nat square double 3        -- 36
```

## Local Definitions (ローカルな定義)

キーワード ``let`` を使うと「ローカルな」定義を導入することができる。式 ``let a := t1; t2`` は ``t2`` の中に現れる全ての ``a`` を ``t1`` で置き換えたものとdefinitionally equalである。

```lean
#check let y := 2 + 2; y * y   -- Nat
#eval  let y := 2 + 2; y * y   -- 16

def double_square (x : Nat) : Nat :=
  let y := x + x; y * y

#eval double_square 2   -- 16
```

``y * y`` の中に現れる全ての ``y`` を ``x + x`` で置き換えることにより、``double_square x`` は項 ``(x + x) * (x + x)`` とdefinitionally equalであることが分かる。``let`` 文を繋げることで、複数のローカルな定義を組み合わせることもできる:

```lean
#check let y := 2 + 2; let z := y + y; z * z   -- Nat
#eval  let y := 2 + 2; let z := y + y; z * z   -- 64
```

改行を挟めば ``;`` を省略することができる。

```lean
def double_square (x : Nat) : Nat :=
  let y := x + x
  y * y
```

式 ``let a := t1; t2`` の意味は ``(fun a => t2) t1`` の意味と非常に似ているが、この2つは同じではないことに注意してほしい。``let a := t1; t2`` において、``t2`` の中に現れる ``a`` は ``t1`` の省略形だと考えるべきである。一方 ``(fun a => t2) t1`` では、``a`` は変数である。したがって、``fun a => t2`` は ``a`` の値に依存せずに意味をなさなければならない。``let`` は強力な省略手法であり、``let a := t1; t2`` とは表現できても ``(fun a => t2) t1`` とは表現できない式が存在する。練習問題として、次の例において、なぜ ``foo`` は型チェックをパスするが ``bar`` は型チェックをパスしないのかを理解してみよう。

```lean
def foo := let a := Nat; fun x : a => x + 2
/-
  def bar := (fun a => fun x : a => x + 2) Nat
-/
```

## Variables and Sections (変数とセクション)

次の3つの関数の定義を考えてみよう:

```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (α : Type) (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (α : Type) (h : α → α) (x : α) : α :=
  h (h (h x))
  
#print compose
#print doTwice
#print doThrice
```

Leanでは、``variable`` コマンドを使うとこのような定義をよりコンパクトにすることができる。``variable (<変数の名前> : <変数の型名>)`` と書くと具体的な関数・定数定義と独立して変数名に型を付けることができる:

```lean
variable (α β γ : Type)

def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (h : α → α) (x : α) : α :=
  h (h (h x))
  
#print compose
#print doTwice
#print doThrice
```

``variable`` を使うと、``Type`` に限らない任意の型を変数に与えることができる:

```lean
variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose := g (f x)
def doTwice := h (h x)
def doThrice := h (h (h x))

#print compose
#print doTwice
#print doThrice
```

``#print <定義の名前>`` コマンドを使うと、指定した定義に関する情報が表示される。``#print`` コマンドを使うと、上の3つの定義グループが同じ3つの関数を定義していることを確認することができる。

``variable`` コマンドは、このコマンドで宣言された変数を参照する定義に、該当変数を束縛変数(入力引数)として挿入するようLeanに指示する。Leanは賢いので、各定義の中でどの変数が明示的あるいは暗黙のうちに使われているかを特定することができる。例えば、Leanは ``doTwice`` の中で変数 ``h`` と ``x`` のみならず、``α`` が使われていることを特定することができる。したがって、``α``、``β``、``γ``、``g``、``f``、``h``、``x`` は指定した型を持つ固定された項であると考えて定義を書けば、後はLeanが自動的に定義を抽象化してくれるのである。

一度 ``variable`` を使って変数が宣言されれば、その変数は宣言されたところから現在のファイルの最後まで有効である。しかしながら、変数のスコープを制限した方が使いやすいときもある。変数のスコープを制限するために、Leanはキーワード ``section`` を提供する:

```lean
section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)
  
  #check α              -- セクション内で変数 `α` は参照可能。
  
  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))
end useful

#check compose          -- セクション内で定義された関数はセクション外でも参照可能。 
-- #check α             -- エラー。セクション外で変数 `α` は参照不可能。
```

例で示した通り、``variable`` を用いてセクション内で宣言された変数は、セクション外ではもはや参照不可能である。

セクション内の行をインデントする必要はない。また、セクションに名前を付ける必要もない。つまり、無名の ``section`` と ``end`` を使うことができる。ただし、セクションに名前を付けた場合は、同じ名前を使ってセクションを閉じる必要がある。また、セクションは入れ子にすることができ、入れ子になったセクションを使うと段階的に新しい変数を宣言することができる。

## Namespaces (名前空間)

キーワード ``namespace`` を使うと、入れ子にできる階層的な名前空間を作ることができ、その中に定義を入れて定義をグループ化することができる:

```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
  def ffa : Nat := f (f a)

  #check a
  #check f
  #check fa
  #check ffa
  #check Foo.fa
end Foo

-- #check a  -- error
-- #check f  -- error
#check Foo.a
#check Foo.f
#check Foo.fa
#check Foo.ffa

open Foo

#check a
#check f
#check fa
#check Foo.fa
```

名前空間 ``Foo`` 内で宣言した全ての識別子(定義の名前)は、宣言時の名前の頭に "``Foo.``" を付けたフルネームを持つ。名前空間 ``Foo`` の中では、"``Foo.``" を省略した短い名前で識別子を参照することができる。しかし、名前空間 ``Foo`` の外では、"``Foo.``" を省略しないフルネームを使って識別子を参照しなければならない。セクションとは違い、名前空間には名前を付ける必要がある。Leanにおいて、ただ1つの無名の名前空間はルートレベルに存在する。これ以外に無名の名前空間の存在は許されない。

``open <名前空間名>`` コマンドを使うと、"``<名前空間名>.``" を省略した短い名前を使えるようになる。モジュール(外部ファイル)をインポートしたときは、短い名前を使うためにそのモジュールが含む名前空間を開きたくなるかもしれない。一方で、開きたい名前空間A内のある識別子 ``A.bar`` と他の名前空間B内の使用したい識別子 ``B.bar`` が衝突するときは、名前空間を開かず、そのような定義をフルネームで保護されたままにしておきたいと思うかもしれない。このように、名前空間は作業環境において名前を管理する方法を提供する。

例えば、Leanはリストに関する定義と定理を名前空間 ``List`` の中でグループ化している。

```lean
#check List.nil
#check List.cons
#check List.map
```

``open List`` を使うと、これらの定義に短い名前でアクセスできるようになる:

```lean
open List

#check nil
#check cons
#check map
```

セクションのように、名前空間は入れ子にすることができる:

```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a

  namespace Bar
    def ffa : Nat := f (f a)

    #check fa
    #check ffa
  end Bar

  #check fa
  #check Bar.ffa
end Foo

#check Foo.fa
#check Foo.Bar.ffa

open Foo

#check fa
#check Bar.ffa
```

``namespace <名前空間名>``を用いることで、名前空間は閉じた後再び開くことができる。インポート元の名前空間をインポート先で開くことさえできる。

```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
end Foo

#check Foo.a
#check Foo.f

namespace Foo
  def ffa : Nat := f (f a)
end Foo

#check Foo.ffa
```

閉じられた名前空間は、例え他のファイルの中であっても、再び開くことができる:

```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
end Foo

#check Foo.a
#check Foo.f

namespace Foo
  def ffa : Nat := f (f a)
end Foo
```

セクションと同様、入れ子になった名前空間は開かれた順に閉じられなければならない。名前空間とセクションは異なる役割を持つ: 名前空間はデータを整理し、セクションは定義に挿入される変数の宣言を整理する。セクションは ``set_option`` や ``open`` のようなコマンドのスコープを区切るのにも便利である。

しかしながら、多くの側面で ``namespace ... end`` ブロックは ``section ... end`` ブロックと同様に振る舞う。特に、名前空間内で ``variable`` コマンドを使った場合、そのスコープは名前空間内に限定される。同様に、名前空間内で ``open`` コマンドを使った場合、``open`` コマンドの効果はその名前空間が閉じられたときに切れる。

## What makes dependent type theory dependent? (何が依存型理論を依存たらしめているのか？)

「型はパラメータ(引数)に依存することができる」、これが簡潔な説明である。既に良い例を見てきた: 型 ``List α`` は引数 ``α`` に依存し、この依存性こそが ``List Nat`` と ``List Bool`` を区別する。別の例として、型 ``Vector α n`` について考えてみよう。``Vector α n`` は型 ``α`` の項からなる長さ ``n`` のベクトル(動的配列)の型である。この型は**2つの**パラメータ、ベクトルの要素の型 ``α : Type`` とベクトルの長さ ``n : Nat`` に依存する。

今、リストの先頭に新しい要素を挿入する関数 ``cons`` を作りたいとしよう。``cons`` はどんな型を持つだろうか。このような関数は**多相**であってほしい: ``cons`` 関数は ``Nat``、``Bool``、ひいては任意の型 ``α`` に対して同様に動作してほしい。これは、``cons`` は最初の引数として型 ``α`` をとるべきであることを意味する。そうすれば、任意の型 ``α`` に対して、``cons α`` は型 ``α`` の項からなるリスト ``List α`` のための挿入関数となる。さらに、挿入する要素 ``a : α`` と ``a`` が挿入されるリスト ``as : List α`` が引数として必要だろう。これらの引数があれば、``cons`` は ``a`` を ``as`` の先頭に挿入した新しいリストを作り、出力することができる。したがって ``cons α a as : List α`` という形の定義が適切だと考えられる。

``cons α`` が型 ``α → List α → List α`` を持つべきなのは明らかである。それでは、型を与える前の ``cons`` はどんな型を持つべきだろうか。``cons`` の持つ型として最初に思いつくのは ``Type → α → List α → List α`` だろう。しかしこれは意味をなさない: ``α`` は ``Type`` 型の引数を参照すべきだが、``Type → α → List α → List α`` 内の ``α`` は何も参照しない。言い換えれば、``α`` と ``List α`` の意味は型 ``Type`` の引数によって決まるが、``Type → α → List α → List α`` は型 ``Type`` の引数に関する情報を持たない。つまり、``α`` と ``List α`` は最初の引数 ``α : Type`` に依存しているのである。実際に ``cons`` の型を ``#check`` で確認してみよう。

```lean
def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat        -- Nat → List Nat → List Nat
#check cons Bool       -- Bool → List Bool → List Bool
#check cons            -- (α : Type) → α → List α → List α
```

これは*dependent function type*(依存関数型)あるいは*dependent arrow type*(依存矢印型)の一例である。``α : Type`` と ``β : α → Type`` があるとき、``β`` は ``α`` 上の型の族だと思ってほしい。つまり、項 ``β : α → Type`` を任意の ``a : α`` に ``β a : Type`` を割り当てる関数だと考えるのである。このとき、型 ``(a : α) → β a`` は任意の ``a : α`` に型 ``β a`` の項 ``f a`` を割り当てる関数 ``f`` の型を表す。言い換えると、関数 ``f`` によって返される値 ``f a`` の型 ``β a`` は入力 ``a`` に依存して変わる。``(a : α) → β a`` という記法は、入力に依存して出力の型が変わるような関数の型を記述することができるのである。

``(a : α) → β`` という依存関数型の記法は、任意の式 ``β`` に対して、たとえ ``β`` が引数 ``a : α`` に依存して変わるときでも、意味をなすのである。これは ``α → β`` という単純関数型の記法は ``β`` が引数 ``a : α`` に依存して変わるときには意味をなさないことと対照的である。つまり、依存関数型は単純関数型より表現の幅が広い。``β`` が ``a`` に依存しないときは、型 ``(a : α) → β`` と 型 ``α → β`` に違いはない。実際、依存型理論において、そしてLeanにおいて、``α → β`` という記法は、``β`` が ``a : α`` に依存しないときの ``(a : α) → β`` の略記に過ぎない。

リストの例に戻る。``#check`` コマンドを使うと、以下の ``List`` に関する関数の型をチェックすることができる。
記号 ``@``、それから括弧 ``()`` と波括弧 ``{}`` の違いについてはすぐ後で説明する。

```lean
#check @List.cons    -- {α : Type u_1} → α → List α → List α
#check @List.nil     -- {α : Type u_1} → List α
#check @List.length  -- {α : Type u_1} → List α → Nat
#check @List.append  -- {α : Type u_1} → List α → List α → List α
```

``β`` が ``α`` に依存できるようにすることで依存関数型 ``(a : α) → β a`` が関数型 ``α → β`` を一般化するのと同様に、依存積型 ``(a : α) × β a`` は直積型 ``α × β`` を一般化する。依存積型は ``β`` が ``a`` に依存することを可能にする。依存積型は*sigma*(Σ)型とも呼ばれ、``(a : α) × β a`` は ``Σ a : α, β a`` とも書かれる。Leanにおいて、``⟨a, b⟩`` あるいは ``Sigma.mk a b`` と書くと依存ペアを作ることができる。`⟨` は ``\langle`` または ``\<`` と打つと入力でき、`⟩` は ``\rangle`` または ``\>`` と打つと入力できる。

```lean
universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b

#print f
#print g

def h1 (x : Nat) : Nat :=
  (f Type (fun α => α) Nat x).2

#eval h1 5 -- 5

def h2 (x : Nat) : Nat :=
  (g Type (fun α => α) Nat x).2

#eval h2 5 -- 5

def i : Type :=                 -- iは ``Nat`` 型のこと
  (f Type (fun α => α) Nat 5).1

def test : i := 5 + 5

#eval test -- 10
```

上記の ``f`` と ``g`` は同じ関数である。


## Implicit Arguments (暗黙の引数)

次のようなリストの実装 ``Lst`` があるとする:

```lean
# universe u
# def Lst (α : Type u) : Type u := List α
# def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
# def Lst.nil (α : Type u) : Lst α := List.nil
# def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
#check Lst          -- Lst.{u} (α : Type u) : Type u
#check Lst.cons     -- Lst.cons.{u} (α : Type u) (a : α) (as : Lst α) : Lst α
#check Lst.nil      -- Lst.nil.{u} (α : Type u) : Lst α
#check Lst.append   -- Lst.append.{u} (α : Type u) (as bs : Lst α) : Lst α
```

このとき、次のように ``Nat`` の項からなるリストを作ることができる:

```lean
# universe u
# def Lst (α : Type u) : Type u := List α
# def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
# def Lst.nil (α : Type u) : Lst α := List.nil
# def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
# #check Lst          -- Type u_1 → Type u_1
# #check Lst.cons     -- (α : Type u_1) → α → Lst α → Lst α
# #check Lst.nil      -- (α : Type u_1) → Lst α
# #check Lst.append   -- (α : Type u_1) → Lst α → Lst α → Lst α
#check Lst.cons Nat 0 (Lst.nil Nat)      -- Lst Nat
#eval Lst.cons Nat 0 (Lst.nil Nat)       -- [0]

def as : Lst Nat := Lst.nil Nat
def bs : Lst Nat := Lst.cons Nat 5 (Lst.nil Nat)

#check Lst.append Nat as bs              -- Lst Nat
#eval Lst.append Nat as bs               -- [5]
```

``Lst`` とそのコンストラクタ ``Lst.cons``、``Lst.nil``、``Lst.append`` は型について多相であるため、これらを使うときは毎回型 ``Nat`` を引数として与えなければならない。しかし、この情報は冗長である。``Lst.cons Nat 5 (Lst.nil Nat)`` について考えてみよう。第二引数が ``5 : Nat`` であることから、``α``　が ``Nat`` であることは容易に推論できる。同様に、``Lst.cons Nat 5 (Lst.nil Nat)`` の ``Lst.nil`` の引数が ``Nat`` であることも、``Lst.cons`` の引数の情報 ``(as : Lst α)`` と ``α`` が ``Nat`` であることを照らし合わせれば分かる。

言わば、たとえ ``Lst.cons Nat 5 (Lst.nil Nat)`` が虫に食われて ``Lst.cons _ 5 (Lst.nil _)`` となっていたとしても、各 ``_`` に入る型が何であるか推論できるのである。

これは依存型理論の中心的な特徴である: 項は多くの情報を持つ。そしていくつかの失われた情報は文脈から推論できる。Leanでは、アンダースコア ``_`` を使うことで、ここの情報を自動で埋めてほしいとシステムに指示することができる。これは「implicit argument(暗黙の引数)」と呼ばれている。次に例を挙げる:

```lean
# universe u
# def Lst (α : Type u) : Type u := List α
# def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
# def Lst.nil (α : Type u) : Lst α := List.nil
# def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
# #check Lst          -- Type u_1 → Type u_1
# #check Lst.cons     -- (α : Type u_1) → α → Lst α → Lst α
# #check Lst.nil      -- (α : Type u_1) → Lst α
# #check Lst.append   -- (α : Type u_1) → Lst α → Lst α → Lst α
#check Lst.cons _ 0 (Lst.nil _)      -- Lst Nat

def as : Lst Nat := Lst.nil _
def bs : Lst Nat := Lst.cons _ 5 (Lst.nil _)

#check Lst.append _ as bs            -- Lst Nat
```

見事に推論に成功している。

しかし、アンダースコアをいちいち入力するのはやはり面倒である。関数が一般的に文脈から推論できる引数をとる場合、「この引数は(デフォルトでは)暗黙のうちに推論してほしい引数である」とLeanに指示することができる。次のように波括弧 ``{}`` で引数をくくると、その引数を暗黙の引数とすることができる:

```lean
universe u
def Lst (α : Type u) : Type u := List α

def Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil {α : Type u} : Lst α := List.nil
def Lst.append {α : Type u} (as bs : Lst α) : Lst α := List.append as bs

#check Lst.cons 0 Lst.nil      -- Lst Nat

def as : Lst Nat := Lst.nil
def bs : Lst Nat := Lst.cons 5 Lst.nil

#check Lst.append as bs        -- Lst Nat
```

変わったのは、関数の定義において ``α : Type u`` を波括弧で囲んだことだけである。他の例も挙げる:

```lean
universe u
def ident {α : Type u} (x : α) := x

#check ident         -- ?m → ?m
#check ident 1       -- Nat
#check ident "hello" -- String
#check @ident        -- {α : Type u_1} → α → α
```

この例では、関数 ``ident`` の第1引数が暗黙の引数になっている。こうすることで、型の指定が隠され、見かけ上 ``ident`` が任意の型の引数を取るように見える。実際、``ident`` と同じ機能を持つ関数 ``id`` は標準ライブラリ内でこのように定義されている。今回は、名前の衝突を避けるため、伝統的でない名前 ``ident`` を用いた。

``variable`` コマンドを使ったときも、変数を暗黙の引数として指定することができる。

```lean
universe u

section
  variable {α : Type u}
  variable (x : α)
  def ident := x
end

#check ident           -- {α : Type u_1} → α → α
#check ident 4         -- Nat
#check ident "hello"   -- String
```

この ``ident`` の定義は一つ上の定義と同じ効果を持つ。

Leanには暗黙の引数を推論するための非常に複雑なメカニズムがあり、それを使うと関数型や述語、さらには証明を推論できることを見ていく。このような「穴」または「プレースホルダー」を埋めるプロセスは、*elaboration*としてよく知られている。暗黙の引数の存在により、ある式の意味を正確に確定させるための情報が不十分である状況が起こりうる。``id`` や ``List.nil`` のような表現は、文脈によって異なる意味を持つことがあるため、*polymorphic*(多相的)であると言われる。

式 ``e`` の型 ``T`` は、``(e : T)`` と書くことで指定できる。これはLeanのelaboratorに、暗黙の引数の解決を試みるとき、``e`` の型として ``T`` を使うように指示する。以下の4行目と5行目では、``id`` と ``List.nil`` の型を思い通りに指定するために、このメカニズムが使われている:

```lean
#check List.nil               -- List ?m
#check id                     -- ?m → ?m

#check (List.nil : List Nat)  -- List Nat
#check (id : Nat → Nat)       -- Nat → Nat
```

Leanでは数字はオーバーロードされる。しかし数字の型が推論できない場合、Leanはデフォルトでその数字の型は自然数であると仮定する。次の例の1行目にはその機能の実例が示されている。3行目では数字の型が指定されているため、1行目と2行目とは異なり ``2`` の型が ``Int`` であると推論されている。

```lean
#check 2            -- Nat
#check (2 : Nat)    -- Nat
#check (2 : Int)    -- Int
```

しかし、ある関数の引数を暗黙の引数として宣言しておきながら、その引数を明示的に与えたいという状況に陥ることがある。``foo`` がそのような関数である場合、``@foo`` という表記は、すべての引数を明示的にした同じ関数を表す。

```lean
#check @id        -- {α : Sort u_1} → α → α
#check @id Nat    -- Nat → Nat
#check @id Bool   -- Bool → Bool

#check @id Nat 1     -- Nat
#check @id Bool true -- Bool
```

最初の ``#check`` コマンドは、何のプレースホルダーも与えていない状態での恒等関数 ``id`` そのものの型を表していることに注意してほしい。さらに、``#check`` コマンドの表示は、第1引数が暗黙の引数であること波括弧を用いて示している。
