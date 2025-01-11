# Interacting with Lean (Leanとの対話)

数学的オブジェクトを定義するための言語としての、そして証明を構築するための言語としての依存型理論の基本は理解していただけただろう。読者がまだ手にしていないのは、新しいデータ型を定義する方法である。このギャップを埋めるため、次の章では*inductive data type*(帰納データ型)の概念を紹介する。その前に、この章では型理論そのものの説明は一旦お休みして、Leanのコードを書く際の実用的な機能について学ぶ。

ここに掲載されている情報の全てが、すぐ役に立つとは限らない。この章は軽く読んでLeanの特徴を掴み、後で必要に応じて戻ってくることをお勧めする。

## Importing Files (ファイルのインポート)

Leanのフロントエンドの目的は、ユーザーの入力を解釈し、形式的な式を構築し、そしてそれらが正しい構文規則に従っており、正しく型付けされることをチェックすることである。Leanは様々なエディタでの使用をサポートしており、ユーザーはエディタ上で継続的なチェックとフィードバックを受けることができる。詳しくはLeanの[documentation pages](http://lean-lang.org/documentation/)を参照してほしい。

Leanの標準ライブラリの定義と定理は複数のファイルに散在している。ユーザーは追加のライブラリを使用したり、複数のファイルからなる独自のプロジェクトを開発することができる。Leanが起動すると、ライブラリの ``Init`` フォルダの内容が自動的にインポートされる。``Init`` フォルダには基本的な定義や構文が多数含まれている。その結果、ここで紹介する例のほとんどは追加設定なしでそのまま動作する。

しかし、追加ファイルを使いたい場合は、ファイルの先頭に ``import`` 文を書いて手動でインポートする必要がある。コマンド

```
import Bar.Baz.Blah
```

は ``Bar/Baz/Blah.olean`` ファイルを読み込む(``.olean`` はコンパイル済のLeanファイルの拡張子である)。このコマンドにおいて、``Bar.Baz.Blah`` はLeanの*search path*(検索パス)からの相対パスとして解釈される。検索パスがどのように決定されるかについては、[documentation pages](http://lean-lang.org/documentation/)を参照してほしい。デフォルトでは、標準ライブラリディレクトリと、場合によってはユーザーのローカルプロジェクトのルートが検索パスに含まれる。(Lean4では、カレントディレクトリからの相対パスでインポートファイルを指定することは**できない**。)

インポートは「推移的」である。言い換えれば、``Foo`` をインポートして、``Foo`` が ``Bar`` をインポートする場合、``Bar`` の内容にもアクセスできるようになる。したがって、``Bar`` を明示的にインポートする必要はない。

## More on Sections (セクションの詳細)

Leanは理論の構造化を手助けするために、様々なセクション分けの仕組みを提供している。[Variables and Sections (変数とセクション)](./dependent_type_theory.md#variables-and-sections-変数とセクション)の節で、``section`` コマンドを使うことで、理論の要素をグループ化できるだけでなく、必要に応じて定理や定義の引数として挿入される変数のスコープを区切ることができることを説明した。``variable`` コマンドのポイントは、次の例のように、定理で使う変数を宣言できることであることを思い出してほしい:

```lean
section
variable (x y : Nat)

def double := x + x

#check double y
#check double (2 * x)

attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

theorem t1 : double (x + y) = double x + double y := by
  simp [double]

#check t1 y
#check t1 (2 * x)

theorem t2 : double (x * y) = double x * y := by
  simp [double, Nat.add_mul]

end
```

``variable (x y : Nat)`` が書かれていれば、``double`` の定義において ``x`` を引数として宣言する必要はない。Leanは ``double`` の定義の中で ``x`` が使われていることを検出し、``(x : Nat)`` を定義の引数に自動的に挿入する。同様に、Leanは ``t1`` と ``t2`` の中に ``x`` と ``y`` が現れることを検出し、 ``(x : Nat)`` と ``(y : Nat)`` を自動的に挿入する。``double`` の定義の中に ``y`` は現れていないため、``double`` は ``y`` を引数として持た**ない**ことに注意してほしい。``variable`` コマンドで宣言された変数は、それらが実際に使用される定義宣言にのみ引数として挿入される。

## More on Namespaces (名前空間の詳細)

Leanでは、識別子(定義や定理や定数の名前)は ``Foo.Bar.baz`` のような*hierarchical names*(階層名)で与えられる。Leanが階層名を扱うためのメカニズムを提供していることは、[Namespaces (名前空間)](./dependent_type_theory.md#namespaces-名前空間)の節で説明した。コマンド ``namespace foo`` は、``end foo``に行き当たるまで、各定義と定理の名前の前に ``foo`` を付加する。コマンド ``open foo`` は、接頭辞 ``foo`` で始まる各定義と定理に、元の「フルネーム」に加えて接頭辞 ``foo`` を除いた一時的な「別名」を与える。

```lean
namespace Foo
def bar : Nat := 1
end Foo

open Foo

#check bar
#check Foo.bar
```

次のような定義

```lean
def Foo.bar : Nat := 1
```

はマクロとして扱われ、次のように展開される。

```lean
namespace Foo
def bar : Nat := 1
end Foo
```

定理や定義の名前は一意でなければならないが、短い「別名」は一意でないことがある。名前空間を開いたとき、識別子の指示対象が曖昧になる可能性がある。Leanは型情報を使って文脈上の意味を曖昧でなくしようとするが、フルネームを記すことで常に曖昧さをなくすことができる。全ての識別子にフルネームを与えるため、空の接頭辞を明示的に記述するための文字列 ``_root_`` が存在する。

```lean
def String.add (a b : String) : String :=
  a ++ b

def Bool.add (a b : Bool) : Bool :=
  a != b

def add (α β : Type) : Type := Sum α β

open Bool
open String
-- #check add -- これは曖昧である
#check String.add           -- String → String → String
#check Bool.add             -- Bool → Bool → Bool
#check _root_.add           -- Type → Type → Type

#check add "hello" "world"  -- String
#check add true false       -- Bool
#check add Nat Nat          -- Type
```

``protected`` キーワードを使って定義を宣言することで、短い別名が作られることを防ぐことができる:

```lean
protected def Foo.bar : Nat := 1

open Foo

-- #check bar -- error
#check Foo.bar
```

一般的な名前のオーバーロードを防ぐため、``protected`` キーワードは ``Nat.rec`` や ``Nat.recOn`` のような名前にも用いられる。

``open`` コマンドにはバリエーションがある。コマンド ``open Nat (succ zero gcd)`` は列挙された識別子 ``succ zero gcd`` に対してのみ短い別名を生成する:

```lean
open Nat (succ zero gcd)
#check zero     -- Nat
#eval gcd 15 6  -- 3
```

コマンド ``open Nat hiding succ gcd`` は、  ``Nat`` 名前空間内の列挙された識別子 ``succ gcd`` を**除く**全てに対して短い別名を生成する:

```lean
open Nat hiding succ gcd
#check zero     -- Nat
-- #eval gcd 15 6  -- error
#eval Nat.gcd 15 6  -- 3
```

コマンド ``open Nat renaming mul → times, add → plus`` は、``Nat.mul`` を ``times`` に、``Nat.add`` を ``plus`` にリネームした上で短い別名を生成する:

```lean
open Nat renaming mul → times, add → plus
#eval plus (times 2 2) 3  -- 7
-- #eval mul 1 2          -- error
#eval Nat.mul 1 2         -- 2
```

ある名前空間から別の名前空間へ、あるいはルートレベルへ別名を ``export`` することは時に便利である。現在の名前空間 ``Foo`` の中で、コマンド ``export Nat (succ add sub)`` は、``Nat.succ``、``Nat.add``、``Nat.sub`` に対して別名 ``Foo.succ``、``Foo.add``、``Foo.sub`` を生成する。したがって、名前空間が開かれているときは、いつでもこれらの別名を使うことができる。名前空間の外で ``export`` コマンドが使われたときは、短い別名がルートレベルにエクスポートされる。

```lean
namespace Foo
export And (intro left right)

#check And.intro  -- And.intro {a b : Prop} (left : a) (right : b) : a ∧ b
#check Foo.intro  -- And.intro {a b : Prop} (left : a) (right : b) : a ∧ b
#check intro      -- And.intro {a b : Prop} (left : a) (right : b) : a ∧ b
#check left       -- And.left {a b : Prop} (self : a ∧ b) : a
end Foo

-- #check intro   -- error

export And (intro left right)
#check intro      -- And.intro {a b : Prop} (left : a) (right : b) : a ∧ b
-- #check _root_.intro  -- error
```

``export`` コマンドが上手く機能しない場合は、``protected`` キーワードや属性によって保護されている可能性を考えよう。

## Attributes (属性)

Leanの主な機能はユーザーの入力を形式的な式に翻訳することであり、その形式的な式はカーネルによって正しさがチェックされ、後で使用するために環境に保存される。しかし、いくつかのコマンドは、環境内のオブジェクトに属性を割り当てたり、記法を定義したり、[10章 Type Classes (型クラス)](./type_classes.md)で説明される型クラスのインスタンスを宣言したりと、環境に別の影響を与える。そのようなコマンドのほとんどはグローバルな効果を持つ、つまり現在のファイル内だけでなく、現在のファイルをインポートした任意のファイル内でその効果が持続する。しかしながら、このようなコマンドは ``local`` 修飾子をサポートしていることが多い。``local`` 修飾子を使えば、コマンドの効果を現在のセクションや名前空間が閉じられるまで、あるいは現在のファイルの終わりまでに限定することができる。

[Using the Simplifier (単純化器の使用)](./tactics.md#using-the-simplifier-単純化器の使用)の節では、定理に ``[simp]`` 属性を付与することで、単純化器がそれらの定理を使用できるようになることを説明した。次の例では、リストの「接頭辞関係」を定義し、この関係が反射的であることを証明し、その定理に ``[simp]`` 属性を割り当てている。

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

@[simp] theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp
```

それから、単純化器は ``isPrefix [1, 2, 3] [1, 2, 3]`` を ``True`` に書き換えることでこれを証明している。

定義がなされた後ならいつでも、その定義に属性を割り当てることができる:

```lean
# def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
#  ∃ t, l₁ ++ t = l₂
theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

attribute [simp] List.isPrefix_self
```

``local`` 修飾子を付けなかった場合、属性は、属性の宣言が行われたファイルをインポートするどのファイルにおいても有効である。``local`` 修飾子を付加すると、属性のスコープは制限される:

```lean
# def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
#  ∃ t, l₁ ++ t = l₂
section

theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

attribute [local simp] List.isPrefix_self

example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp

end

-- Error:
-- example : isPrefix [1, 2, 3] [1, 2, 3] := by
--  simp
```

他の例として、``instance`` コマンドを使うと ``isPrefix`` 関係に ``≤`` という表記を割り当てることができる。[10章 Type Classes (型クラス)](./type_classes.md)で説明するが、``instance`` コマンドは関連する定義に ``[instance]`` 属性を割り当てることで機能する。

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

instance : LE (List α) where
  le := isPrefix

theorem List.isPrefix_self (as : List α) : as ≤ as :=
  ⟨[], by simp⟩
```

``instance`` を用いた表記の割り当てもローカルにすることができる:

```lean
# def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
#   ∃ t, l₁ ++ t = l₂
def instLe : LE (List α) :=
  { le := isPrefix }

section
attribute [local instance] instLe

example (as : List α) : as ≤ as :=
  ⟨[], by simp⟩

end

-- Error:
-- example (as : List α) : as ≤ as :=
--  ⟨[], by simp⟩
```

後述の[Notation (記法)](#notation-記法)の節では、Leanの記法を定義するメカニズムについて説明し、このメカニズムが ``local`` 修飾子もサポートしていることを確認する。しかし、以下の[Setting Options (オプションの設定)](#setting-options-オプションの設定)の節でLeanのオプション設定のメカニズムを説明するが、これは今までのパターンに従って**いない**: オプションはローカルに設定すること**しかできない**。つまり、オプション設定のスコープは常に現在のセクションかファイルに限定される。

## More on Implicit Arguments (暗黙の引数の詳細)

[Implicit Arguments (暗黙の引数)](./dependent_type_theory.md#implicit-arguments-暗黙の引数)の節で、Leanにおいて項 ``t`` の型を ``{x : α} → β x`` と表すとき、波括弧は ``x`` が ``t`` の暗黙の引数であることを表す、と説明した。これは、``t`` が記述されたときは常にその後にプレースホルダー(穴)が挿入されることを、つまり ``t`` が ``@t _`` に置換されることを意味する。それを望まない場合は、 ``t`` の代わりに ``@t`` と書く必要がある。

暗黙の引数は貪欲に、可能な限り挿入されることに注意してほしい。``y`` だけを暗黙の引数にして関数 ``f (x : Nat) {y : Nat} (z : Nat)`` を定義したとする。このとき、2番目以降の引数を書かずに ``f 7`` と書くと、これは構文解析器(パーサ)により ``f 7 _`` とパースされる。Leanは弱い暗黙の引数(より控えめに挿入される暗黙の引数)を指定する記法 ``{{y : Nat}}`` を提供している。これは当該引数の後ろに明示的な引数がある場合にのみ、その明示的な引数の**前に**プレースホルダーを追加することを指定する。この記法は ``⦃y : Nat⦄`` と書くこともでき、このunicode括弧はそれぞれ ``\{{`` と ``\}}`` と打つと入力できる。``f (x : Nat) ⦃y : Nat⦄ (z : Nat)`` と書いた場合、``f 7`` はそのままパースされ、``f 7 3`` は ``f 7 _ 3`` とパースされる。

この違いを説明するために、反射的ユークリッド関係が対称的かつ推移的であることを示す次の例を考えてみよう。

```lean
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b : α}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r b c → r a c

def euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : symmetric r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr a)

theorem th2 {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : euclidean r)
            : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  show r a c from euclr (symmr rab) rbc

theorem th3 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : transitive r :=
 th2 (th1 reflr @euclr) @euclr

variable (r : α → α → Prop)
variable (euclr : euclidean r)

#check @euclr  -- euclidean r
#check euclr   -- r ?m1 ?m2 → r ?m1 ?m3 → r ?m2 ?m3
```

この例は3つの小さなステップからなっている: ``th1`` は反射的かつユークリッド的な関係が対称的であることを示す。``th2`` は対称的かつユークリッド的な関係が推移的であることを示す。そして ``th3`` は2つの定理を組み合わせ、反射的かつユークリッド的な関係が推移的であることを示している。しかし、``th3`` の証明において、``euclr`` の暗黙の引数を手動で無効にしなければならない。そうしなければ、証明中の ``euclr`` に必要以上に多くの暗黙の引数が挿入されてしまうからである。つまり、証明内の ``@euclr`` は命題 ``∀ {a b c : α}, r a b → r a c → r b c`` の証明項である一方で、証明内の ``euclr`` は ``@euclr`` を暗黙のメタ引数 ``?m1 ?m2 ?m3 : α`` に適用してできた、命題 ``r ?m1 ?m2 → r ?m1 ?m3 → r ?m2 ?m3`` の証明項なのである。弱い暗黙の引数を使えばこの問題は解決する:

```lean
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b : α}}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r b c → r a c

def euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : symmetric r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr a)

theorem th2 {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : euclidean r)
            : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  show r a c from euclr (symmr rab) rbc

theorem th3 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : transitive r :=
 th2 (th1 reflr euclr) euclr

variable (r : α → α → Prop)
variable (euclr : euclidean r)

#check @euclr  -- euclidean r
#check euclr   -- euclidean r
```

角括弧 ``[`` と ``]`` で表される3種類目の暗黙の引数がある。[10章 Type Classes (型クラス)](./type_classes.md)で説明するように、これらは型クラスのために用いられる。

## Notation (記法)

Leanの識別子には、ギリシャ文字を含む任意の英数字(依存型理論で特別な意味を持つ∀、Σ、λは除く)を使うことができる。また、``\_`` と打った後に希望の添字を打つことで、添字を入力することもできる。

Leanのパーサは拡張可能である、つまり、ユーザーは新しい記法を定義することができる。

ユーザーは、Leanの構文を、基本的な*mixfix*記法からユーザーカスタムのelaboratorまで、あらゆるレベルで拡張したりカスタマイズできる。実際、全てのビルトイン構文は、ユーザー向けに提供されているメカニズムやAPIと同じものを使ってパースされ、処理される。この節では、様々な拡張方法について記述し、説明する。

新しい記法を導入することは、プログラミング言語では比較的まれなことであり、コードを不明瞭にする可能性があるため時には嫌われることさえあるが、形式化においては、各分野で確立された慣習や記法をコードで簡潔に表現するための非常に貴重なツールである。基本的な記法にとどまらず、よくある定型的なコードを抽出して(うまく機能する)マクロに落とし込んだり、カスタムされたドメイン固有言語(DSL)全体を組み込んで部分問題を効率的かつ読みやすくテキストにエンコードするLeanの機能は、プログラマーと証明エンジニアの双方にとって大きなベネフィットとなる。

### Notations and Precedence (記法と優先順位)

最も基本的な構文拡張コマンドを使うと、新しい(あるいはオーバーロードされた)前置演算子、中置演算子、後置演算子を導入することができる。

```lean
infixl:65   " + " => HAdd.hAdd  -- 左結合的な中置演算子
infix:50    " = " => Eq         -- 非結合的な中置演算子
infixr:80   " ^ " => HPow.hPow  -- 右結合的な中置演算子
prefix:100  "-"   => Neg.neg    -- 前置演算子
set_option quotPrecheck false
postfix:max "⁻¹"  => Inv.inv    -- 後置演算子
```

演算子の種類(その「固定位置」)を表す最初のコマンド名とコロン ``:`` の後に、演算子の*parsing precedence*(パース優先順位)を与える。次に新規または既存の記号を二重引用符で囲み(空白はコードの見た目を整えるために使われる)、矢印 ``=>`` の後にこの演算子の変換先の関数を指定する。

優先順位とは演算子と引数の結びつきの「強さ」を表す自然数で、演算の順序を表す。上記がマクロ展開されてできるコマンドを見ることで、これらをより正確に理解することができる:

```lean
notation:65 lhs:65 " + " rhs:66 => HAdd.hAdd lhs rhs
notation:50 lhs:51 " = " rhs:51 => Eq lhs rhs
notation:80 lhs:81 " ^ " rhs:80 => HPow.hPow lhs rhs
notation:100 "-" arg:100 => Neg.neg arg
set_option quotPrecheck false
notation:1024 arg:1024 "⁻¹" => Inv.inv arg  -- ``max`` はパース優先順位1024の略記
```

最初のコードブロックの全てのコマンドは、実際にはより一般的な ``notation`` コマンドに変換するコマンドマクロであることがわかった。このようなマクロの書き方は後の節で学ぶ。``notation`` コマンドは、単一の記号の代わりに、記号と「優先順位を持つ名前付き項プレースホルダー」を組み合わせたシーケンスを受け付ける。このシーケンスは ``=>`` の右辺で参照され、右辺にあるプレースホルダーはシーケンス内の位置に基づいてパースされた各項によって置換される。優先順位 ``p`` を持つプレースホルダーは、その場所で ``p`` 以上の優先順位を持つ表記のみを受け付ける。したがって、文字列 ``a + b + c`` を ``a + (b + c)`` とパースすることはできない。なぜなら、``infixl`` コマンドの演算子の右辺は、演算子自体よりも優先順位が1大きいからである。対照的に、``infixr`` コマンドの演算子の右辺は、演算子と同じ優先順位を持つ。そのため、``a ^ b ^ c`` は ``a ^ (b ^ c)`` とパースされる。優先順位が結合性を明確に決定しない場合、``notation`` コマンドを直接使って次のような中置演算子を導入すると、Leanはこの演算子をデフォルトで右結合的にパースすることに注意してほしい:

```lean
# set_option quotPrecheck false
notation:65 lhs:65 " ~ " rhs:65 => wobble lhs rhs
```

より正確には、曖昧な文法が存在する場合、Leanのパーサはローカルな*longest parse rule*(最長構文解析ルール)に従う: ``a ~ b ~ c`` の中の ``a ~`` の右辺をパースするとき、パーサは(優先順位が許す限り)最も長くパースを続ける。つまり ``b`` をパースした後に停止せず、``~ c`` もパースする。したがって、項 ``a ~ b ~ c`` は ``a ~ (b ~ c)`` と等価である。(Leanのパーサは、あくまで最も左側に位置する演算子から順にパースを試みることに注意してほしい。)

上記で言及したように、``notation`` コマンドを使うと、記号とプレースホルダーを自由にミックスした任意の*mixfix*構文を定義することができる。

```lean
# set_option quotPrecheck false
notation:max "(" e ")" => e
notation:10 Γ " ⊢ " e " : " τ => Typing Γ e τ
```

優先順位が明記されていないプレースホルダーの優先順位はデフォルトで ``0`` であり、つまりその位置にある任意の項を受け入れる。2つの記法が重なる場合、再び最長構文解析ルールを適用する。

```lean
notation:65 a " + " b:66 " + " c:66 => a + b - c
#eval 1 + 2 + 3  -- 0
```

新しい記法は2項記法よりも優先される。なぜなら2項記法はパースが連鎖せず、``1 + 2`` をパースしたところで構文解析をやめてしまうからである。最長のパースを受け入れる記法が複数ある場合、どちらが選択されるかはelaborationまで遅延され、ただ1つのオーバーロード記法が正しい型を持つ場合のみ成功し、それ以外の場合は曖昧さを解決できず失敗する。

## Coercions (型強制)

Leanでは、自然数の型 ``Nat`` と整数の型 ``Int`` は異なる。しかし、自然数を整数の中に埋め込む ``Int.ofNat`` という関数があり、これを使うと必要なときに自然数を整数に変換することができる。Leanはこの種の型変換の必要性を検出して型変換を実行するメカニズムを持っている。このような自動的な型変換を*coercions*(強制)と呼ぶ。

```lean
variable (m n : Nat)
variable (i j : Int)

#check i + m      -- i + Int.ofNat m : Int
#check i + m + j  -- i + Int.ofNat m + j : Int
#check i + m + n  -- i + Int.ofNat m + Int.ofNat n : Int
```

## Displaying Information (情報の表示)

Leanに現在の状態や、現在のコンテキストで利用可能なオブジェクトや定理に関する情報を問い合わせる方法はいくつもある。最も一般的なコマンド ``#check`` と ``#eval`` は既に紹介した。``#check`` は ``@`` 記号と一緒に使われることが多く、こうすると定理や定義の引数を暗黙の引数を含めて全て明示することができる。さらに、``#print`` コマンドを使うと、任意の識別子に関する情報を得ることができる。識別子が定義や定理を表す場合、``#print`` コマンドはその識別子の型と定義式を表示する。識別子が定数や公理である場合、``#print`` コマンドは「この識別子は定数(または公理)である」という事実を示し、その型を表示する。

```lean
-- examples with equality
#check Eq
#check @Eq
#check Eq.symm
#check @Eq.symm

#print Eq.symm

-- examples with And
#check And
#check And.intro
#check @And.intro

-- a user-defined function
def foo {α : Type u} (x : α) : α := x

#check foo
#check @foo
#print foo

-- axiom example
#print propext
```

## Setting Options (オプションの設定)

Leanは、Leanの動作を制御するためにユーザーが設定することができる内部変数をいくつも保持している。そのための構文は次の通り:

```
set_option <name> <value>
```

非常に便利なオプション群の1つは、Leanの*pretty-printer*(プリティプリンタ)が項を表示する方法を制御する。以下のオプションはtrueかfalseを入力として受け取る:

```
pp.explicit  : 暗黙の引数を表示する
pp.universes : 隠れた宇宙パラメータを表示する
pp.notation  : 定義された記法を用いて出力を表示する
```

例として、次のように設定すると、かなり長い出力が得られる:

```lean
#check 2 + 2 = 4
#reduce (fun x => x + 2) = (fun x => x + 3)
#check (fun x => x + 1) 1

set_option pp.explicit true
set_option pp.universes true
set_option pp.notation false

#check 2 + 2 = 4
#reduce (fun x => x + 2) = (fun x => x + 3)
#check (fun x => x + 1) 1
```

コマンド ``set_option pp.all true`` はこれらの設定を一度に実行し、``set_option pp.all false`` はこれらのオプションを元の値に戻す。証明をデバッグするときや、不可解なエラーメッセージを理解しようとするときに、付加的な情報を表示させることはしばしば非常に役に立つ。しかし、情報が多すぎると圧倒されるかもしれない。普通にLeanを使う場合はデフォルトの情報表示で一般的には十分である。

<!--
## Elaboration Hints (elaborationのヒント)

Leanに ``λ x y z, f (x + y) z`` のような式の処理を依頼する場合、暗黙の情報を残していることになる。例えば、``x``、``y``、``z`` の型は文脈から推論する必要があり、``+`` という記法はオーバーロードされている可能性があり、``f`` にも埋める必要のある暗黙の引数があるかもしれない。さらに、[10章 Type Classes (型クラス)](./type_classes.md)では、いくつかの暗黙の引数は*type class resolution*(型クラス解決)として知られているプロセスによって合成されていることが分かる。また、項のいくつかの部分がタクティクフレームワークによって構築されうることも、すでに前章で見てきた。

いくつかの暗黙の引数を推論するのは簡単である。例えば、ある関数 ``f`` が ``Π {α : Type*}, α → α → α`` という型を持ち、Leanが ``f n`` という項を構文解析しようとしているとする。ここで、``n`` は ``nat`` 型を持つと推論できるとすると、暗黙の引数 ``α`` が ``nat`` でなければならないことは明らかである。しかしながら、いくつかの推論問題は*higher order*(高階)である。例えば、等号の置換演算 ``Eq.subst`` は以下の型を持っている:

.. code-block:: text

    Eq.subst : ∀ {α : Sort u} {p : α → Prop} {a b : α},
                 a = b → p a → p b

ここで、``a b : ℕ`` かつ ``h₁ : a = b`` かつ ``h₂ : a * b > a`` だとすると、``eq.subst h₁ h₂``において、``p`` は以下のいずれにもなりうる:

-  ``λ x, x * b > x``
-  ``λ x, x * b > a``
-  ``λ x, a * b > x``
-  ``λ x, a * b > a``

言い換えれば、ユーザーの意図は、``h₂`` の1番目か2番目の ``a`` だけを置き換えること、あるいは両方を置き換えること、あるいはどちらも置き換えないことかもしれない。同様の曖昧さは、帰納述語の推論や関数の引数の推論でも生じる。2階のユニフィケーションでさえ決定不可能であることが知られている。したがって、Leanはヒューリスティクスに依存してそのような引数を推論する。そしてLeanが正しい引数を推論できないときは、引数を明示的に与える必要がある。

さらに悪いことに、定義を展開する必要がある場合もあれば、基礎となる論理フレームワークの計算ルールに従って式を簡約化する必要がある場合もある。もう一度言うが、何をいつ展開し、簡約化するかを決めるために、Leanはヒューリスティクスに頼らなければならない。

しかしながら、elaboratorにヒントを提供するために使用できる属性がある。ある属性群は、定義がどの程度熱心に展開されるかを決定する: 定義・定数(定義された項)には ``[reducible]``、``[semireducible]``、``[irreducible]`` という属性を付けることができる。定義はデフォルトで ``[semireducible]`` とマークされる。``[reducible]`` 属性を付けられた定義は熱心に展開される。もしその定義を省略形として考えるのであれば、``[reducible]`` 属性を付けるのが適切だろう。elaborator は ``[irreducible]`` 属性を持つ定義の展開を避ける。定理はデフォルトで ``[irreducible]`` とマークされる。なぜなら、*proof irrelevance*(証明無関係)の原則により、一般的に証明の中身はelaborationのプロセスに関係ないからである。

これらの属性は、elaboratorへのヒントに過ぎないことを強調しておく。elaborateされた項の正しさをチェックするとき、Leanのカーネルは展開する必要のある定義全てを展開する。他の属性と同様に、上記の属性群は ``local`` 修飾子を付けて指定することができる。そうすれば、これらの属性が現在のセクションまたはファイル内だけで有効になる。

Leanはelaborationの戦略をコントロールする属性も持っている。定義や定理には ``[elab_with_expected_type]``、``[elab_simple]``、``[elab_as_eliminator]`` のいずれかの属性を付けることができる。これらの属性を定義 ``f`` に付けると、引数に ``f`` を適用した式 ``f a b c ...`` のelaborationを行うことができる。デフォルトの属性である ``[elab_with_expected_type]`` では、引数 ``a``、``b``、``c``、... は、 ``f`` と前の引数から推論される、期待される型に関する情報を使ってelaborateされる。一方、``[elab_simple]`` では、各引数の型に関する情報を後続の引数に伝搬することなく、単に左から右へと引数をelaborateしていく。最後の属性である ``[elab_as_eliminator]`` は、帰納器や帰納法原理、``eq.subst`` などの簡約器のためによく使われる。これは高階のパラメータを推論するために別のヒューリスティクスを使用する。このような操作については、次の章で詳しく説明する。

繰り返しになるが、これらの属性はオブジェクトが定義された後ならいつでも割り当てや再割り当てが可能であり、``local`` 修飾子を使ってその範囲を制限することができる。さらに、式の中で識別子の前に ``@`` 記号を書くと、Leanは自動でelaboratorに ``[elab_simple]`` 戦略を使うように指示する。これは、トリッキーなパラメータを明示的に提供する場合は、elaboratorにその情報を重視してもらいたいという考え方である。実際、Leanには ``@@`` という代替記号があり、これは最初の高階引数より前の引数を暗黙のままにしておくものである。例えば、``@@Eq.subst`` は等式の型を暗黙のままにするが、代入のコンテキストは明示する。

-->

## Using the Library (ライブラリの使用)

Leanを効率的に使おうと思ったら、必然的にライブラリにある定義や定理を利用する必要が出てくるだろう。ファイルの先頭に ``import`` コマンドを書くと他のファイルから既にコンパイルされた結果をインポートできることと、インポートは推移的であることを思い出してほしい。現在のファイルが ``Foo`` をインポートし、``Foo`` が ``Bar`` をインポートしているなら、現在のファイルで ``Foo`` のみならず ``Bar`` の定義や定理も利用できる。しかし、名前空間を開くという行為(これによりより短い名前が提供される)はインポート先に引き継がれない。各ファイルで、使用したい名前空間を開く必要がある。

一般に、ライブラリとその内容に詳しくなることは重要である。そうすれば、どのような定理、定義、記法、リソースが利用できるかを知ることができる。Leanのエディタモードも必要なものを見つけるのに役に立つが、ライブラリの内容を直接勉強することはしばしば避けられない。Leanの標準ライブラリはGitHubにあり、オンラインで見ることができる:

- [https://github.com/leanprover/lean4/tree/master/src/Init](https://github.com/leanprover/lean4/tree/master/src/Init)

- [https://github.com/leanprover/std4/tree/main/Std](https://github.com/leanprover/std4/tree/main/Std)

GitHubのブラウザインターフェースを使えば、これらのディレクトリやファイルの内容を見ることができる。自分のコンピュータにLeanをインストールした場合は、``lean`` フォルダの中でライブラリ(例えば、``.../.elan/toolchains/leanprover--lean4---nightly/src/lean/Lean``)を見つけて、ファイルマネージャで探索することができる。各ファイルの先頭にあるコメントヘッダは、ファイルに関する追加情報を提供する。

Leanのライブラリ開発者は一般的な命名ガイドラインに従っている。そのため、ユーザーが必要な定理の名前を推測することや、Leanモードをサポートしているエディタでタブ補完を使って定理を見つけることがより簡単になっている。これらについては次の節で説明する。識別子は通常 ``camelCase`` で、型は ``CamelCase`` で命名される。定理には、異なる構成要素を ``_`` で区切った説明的な名前を宛てている(変数名は省略される)。多くの場合、定理の名前はシンプルに結論だけを表す:

```lean
#check Nat.succ_ne_zero
#check Nat.zero_add
#check Nat.mul_one
#check Nat.le_of_succ_le_succ
```

Leanにおいて、識別子たちは階層的な名前空間の中で整理できることを覚えてほしい。例えば、名前空間 ``Nat`` の中の ``le_of_succ_le_succ`` という定理は ``Nat.le_of_succ_le_succ`` というフルネームを持っているが、コマンド ``open Nat`` を使うことで、(``protected`` とマークされていない名前については)より短い名前が利用可能になる。Leanにおいて、構造体と帰納データ型を定義すると、定義した型に関連する操作が生成され、それらは定義中の型の名前と同じ名前の名前空間に格納されることは、[7章 Inductive Types (帰納型)](./inductive_types.md)と[9章 Structures and Records (構造体とレコード)](./structures_and_records.md)で説明する。例えば、直積型には以下の操作が付属している:

```lean
#check @Prod.mk
#check @Prod.fst
#check @Prod.snd
#check @Prod.rec
```

``Prod.mk`` はペアを構成するために使われる。一方で、``Prod.fst`` と ``Prod.snd`` はそれぞれ直積の1つ目の要素と2つ目の要素を射影する。``Prod.rec`` は直積の2つの構成要素に対する関数から、直積に対する関数を定義するメカニズムを提供する。``Prod.rec`` のような名前は**保護されて**おり、たとえ ``Prod`` 名前空間が開いているときでもフルネームを使用しなければならない。

型としての命題対応において、論理的結合子は帰納型の例である。したがって、論理的結合子に対してドット記法を使うことが多い:

```lean
#check @And.intro
#check @And.casesOn
#check @And.left
#check @And.right
#check @Or.inl
#check @Or.inr
#check @Or.elim
#check @Exists.intro
#check @Exists.elim
#check @Eq.refl
#check @Eq.subst
```

## Auto Bound Implicit Arguments (自動束縛暗黙引数)

以前の節で、暗黙の引数が関数をより便利に使えるようにすることを示した。しかし、``compose`` のような関数はまだ定義が冗長である。宇宙多相的な ``compose`` の定義は2章で定義したものよりもさらに冗長であることに注意してほしい。

```lean
universe u v w
def compose {α : Type u} {β : Type v} {γ : Type w}
            (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

``compose`` を定義するときに宇宙パラメータ ``.{u, v, w}`` を与えることで、``universe`` コマンドを省略することができる。

```lean
def compose.{u, v, w}
            {α : Type u} {β : Type v} {γ : Type w}
            (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

Lean 4は、*auto bound implicit arguments*(自動束縛暗黙引数)という新機能をサポートしている。この機能により、``compose`` のような関数をより便利に書くことができる。Leanが定義宣言の前提を処理するとき、まだ束縛されていない識別子が**1文字の小文字かギリシャ文字であれば**、それらが暗黙引数として自動的に追加される。この機能を使うと、 ``compose`` を次のように書くことができる。

```lean
def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

#check @compose
-- {β : Sort u_1} → {γ : Sort u_2} → {α : Sort u_3} → (β → γ) → (α → β) → α → γ
```

``Type`` の代わりに ``Sort`` を用いることで、Leanはより一般的な型を推論したことに注意してほしい。

私たち(原文筆者たち)はこの機能が大好きで、Leanを実装する際に広く使用しているが、一部のユーザーはこの機能を不快に感じるかもしれないことも認識している。そのため、コマンド ``set_option autoImplicit false`` を使ってこの機能を無効にすることができる。

```lean
set_option autoImplicit false
/- 次の定義は `unknown identifier` エラーを生成する -/
-- def compose (g : β → γ) (f : α → β) (x : α) : γ :=
--   g (f x)
```

## Implicit Lambdas (暗黙ラムダ式)

Lean 3の標準ライブラリでは、``@`` と ``_`` を多用した怖ろしいイディオム(コードパターン)の[実例](https://github.com/leanprover/lean/blob/master/library/init/category/reader.lean#L39)をよく見かける。このイディオムは、期待される型が暗黙引数を持つ関数型で、さらに暗黙引数を取る定数(実例では ``reader_t.pure``)がある場合によく使われる。Lean 4では、elaboratorにより暗黙引数を消費するためのラムダ式が自動的に導入される。私たちはこの機能を探究し、その影響を分析しているところだが、これまでの経験はとてもポジティブなものである。以下は、上記リンクの実例に対してLean 4の暗黙ラムダ式を使った例である。

```lean
# variable (ρ : Type) (m : Type → Type) [Monad m]
instance : Monad (ReaderT ρ m) where
  pure := ReaderT.pure
  bind := ReaderT.bind
```

``@`` を使うか、``{}`` または ``[]`` 束縛記法でラムダ式を書くことで、暗黙ラムダ式機能を無効にすることができる。以下はその例である:

```lean
namespace ex2
def id1 : {α : Type} → α → α :=
  fun x => x

def listId : List ({α : Type} → α → α) :=
  (fun x => x) :: []

-- 次の例において、``fun`` の前に ``@`` があるときは
-- 暗黙ラムダ式導入機能は無効になっている
def id2 : {α : Type} → α → α :=
  @fun α (x : α) => id1 x

def id3 : {α : Type} → α → α :=
  @fun α x => id1 x

def id4 : {α : Type} → α → α :=
  fun x => id1 x

-- 次の例では、束縛記法 ``{...}`` を使っているため、
-- 暗黙ラムダ式導入機能は無効になっている
def id5 : {α : Type} → α → α :=
  fun {α} x => id1 x
end ex2
```

## Sugar for Simple Functions (単純な関数のための糖衣構文)

Lean 3では、括弧を使うことで、中置演算子から簡単な関数を作ることができる。例えば、``(+1)`` は ``fun x, x + 1`` の糖衣構文である。Lean 4では、``·`` をプレースホルダーとして使うことでこの表記を一般化する。以下はその例である:

```lean
# namespace ex3
#check (· + 1)
-- fun a => a + 1
#check (2 - ·)
-- fun a => 2 - a
#eval [1, 2, 3, 4, 5].foldl (·*·) 1
-- 120

def f (x y z : Nat) :=
  x + y + z

#check (f · 1 ·)
-- fun a b => f a 1 b

#eval [(1, 2), (3, 4), (5, 6)].map (·.1)
-- [1, 3, 5]
# end ex3
```

Lean 3と同様、この糖衣構文は括弧を使うことでアクティベートされ、ラムダ抽象は括弧で囲まれた ``·`` を引数として集めることで作られる。引数の収集は、入れ子になった括弧によって中断される。次の例では、2つの異なるラムダ式が生成されている:

```lean
#check (Prod.mk · (· + 1))
-- fun a => (a, fun b => b + 1)
```

## Named Arguments (名前付き引数)

名前付き引数を使うと、引数リスト内の位置と引数をマッチさせるだけでなく、関数定義時に指定された引数名と引数をマッチさせることができる。引数の順番は覚えていないが引数の名前は知っている場合、その名前を使えばどんな順番でもその引数を与えることができる。Leanが暗黙引数を推論できなかった場合、名前付き引数を使ってその暗黙引数の値を指定することもできる。名前付き引数は、各引数が何を表しているのかを明確にすることで、コードの読みやすさも向上させる。

```lean
def sum (xs : List Nat) :=
  xs.foldl (init := 0) (·+·)

#eval sum [1, 2, 3, 4]
-- 10

example {a b : Nat} {p : Nat → Nat → Nat → Prop} (h₁ : p a b b) (h₂ : b = a)
    : p a a b :=
  Eq.subst (motive := fun x => p a x b) h₂ h₁
```

以下に、名前付き引数とデフォルト引数の相互作用を例示する。

```lean
def f (x : Nat) (y : Nat := 1) (w : Nat := 2) (z : Nat) :=
  x + y + w - z
-- ``(y : Nat := 1)`` は ``y`` のデフォルトの値が ``1`` であることを表す

example (x z : Nat) : f (z := z) x = x + 1 + 2 - z := rfl

example (x z : Nat) : f x (z := z) = x + 1 + 2 - z := rfl

example (x y : Nat) : f x y = fun z => x + y + 2 - z := rfl

example : f = (fun x z => x + 1 + 2 - z) := rfl

example (x : Nat) : f x = fun z => x + 1 + 2 - z := rfl

example (y : Nat) : f (y := 5) = fun x z => x + 5 + 2 - z := rfl

def g {α} [Add α] (a : α) (b? : Option α := none) (c : α) : α :=
  match b? with
  | none   => a + c
  | some b => a + b + c

variable {α} [Add α]

example : g = fun (a c : α) => a + c := rfl

example (x : α) : g (c := x) = fun (a : α) => a + x := rfl

example (x : α) : g (b? := some x) = fun (a c : α) => a + x + c := rfl

example (x : α) : g x = fun (c : α) => x + c := rfl

example (x y : α) : g x y = fun (c : α) => x + y + c := rfl
```

``..`` を使えば、足りない明示的引数全てに ``_`` を指定することができる。この機能と名前付き引数を組み合わせると、パターンを書くのに便利である。以下はその例である:

```lean
inductive Term where
  | var    (name : String)
  | num    (val : Nat)
  | app    (fn : Term) (arg : Term)
  | lambda (name : String) (type : Term) (body : Term)

def getBinderName : Term → Option String
  | Term.lambda (name := n) .. => some n
  | _ => none

def getBinderType : Term → Option Term
  | Term.lambda (type := t) .. => some t
  | _ => none
```

省略記号は、明示的な引数が自動的に推論され、かつ ``_`` の連続を避けたい場合にも便利である。

```lean
example (f : Nat → Nat) (a b c : Nat) : f (a + b + c) = f (a + (b + c)) :=
  congrArg f (Nat.add_assoc ..)
```
