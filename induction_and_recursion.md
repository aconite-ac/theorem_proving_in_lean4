# Induction and Recursion (帰納と再帰)

前章では、帰納的定義がLeanに新しい型を導入する強力な手段となることを説明した。さらに言えば、コンストラクタと再帰子(エリミネータ)は、帰納型から他の型への関数を定義する唯一の手段である。型としての命題対応により、この事実は帰納法が証明の基本的な方法であることを意味する。

Leanは再帰関数の定義、パターンマッチングの実行、帰納的証明の記述に対して自然な方法を提供する。関数を定義するには、その関数が満たすべき等式を指定する。定理を証明するには、起こりうる全てのケースをどのように扱うかを指定する。裏では、これらの記述は*equation compiler*(等式コンパイラ)と呼ばれるものを用いて、プリミティブな再帰子へと「コンパイル」される。等式コンパイラはtrusted code base(システムの信頼性保証において最も基礎的で重要なコード)の一部ではない。等式コンパイラの出力はカーネルによって独立にチェックされる項で構成される。

## 用語に関する注意

この節は翻訳に際して追加した節である。

この章では、次のような定義

```lean
open Nat
def foo : Nat → Nat → Nat
  | zero  , zero   => 0
  | zero  , succ y => 1
  | succ x, zero   => 2
  | succ x, succ y => 3
```

があるとき、``zero`` や ``succ y`` などを「パターン(pattern)」、``| zero  , zero`` などを「ケース(case)」、定義として与えられたケース全てをまとめたものを「ケースリスト(list of cases)」、不足なくケースが与えられたケースリストを用いてパターンマッチングすることを「場合分け(by cases)」あるいは「場合分けする(split on cases)」と呼ぶ。

## Pattern Matching (パターンマッチング)

schematic patternsの解釈は、コンパイルの最初のステップである。帰納型のコンストラクタと ``casesOn`` 再帰子を使って、関数を定義したり、場合分けによる定理の証明が行えることを見てきた。しかし、複雑な定義は、入れ子になった ``casesOn`` 適用をいくつも使うことがあり、そのような記述は読みにくく理解しにくいかもしれない。パターンマッチングはより便利で、関数型プログラミング言語ユーザーに馴染みのあるアプローチを提供する。

帰納的に定義された自然数の型について考える。全ての自然数は ``zero`` か ``succ x`` のどちらかの形をとるため、それぞれのケースにおいて出力の値を指定することで、自然数から任意の型への関数を定義することができる:

```lean
open Nat

/- 等式コンパイラによるパターンマッチングを使った関数定義の構文

   この構文を使って帰納型から任意の型への関数を定義する場合、
   `:=` は不要である(書くとコンパイルエラーになる)ことに注意。
   定義したい項が型Tを持つとき、この構文は型Tの(1つ以上の)前件とパターンマッチングする -/

def sub1 : Nat → Nat
  | zero   => zero
  | succ x => x

def isZero : Nat → Bool
  | zero   => true
  | succ x => false
```

以上の関数を定義するために使われる等式の集まり(例えば、``sub1 zero = zero`` は上記の関数定義の一部だとみなせる)はdefinitionallyに成立する:

```lean
# open Nat
# def sub1 : Nat → Nat
#   | zero   => zero
#   | succ x => x
# def isZero : Nat → Bool
#   | zero   => true
#   | succ x => false
example : sub1 0 = 0 := rfl
example (x : Nat) : sub1 (succ x) = x := rfl

example : isZero 0 = true := rfl
example (x : Nat) : isZero (succ x) = false := rfl

example : sub1 7 = 6 := rfl
example (x : Nat) : isZero (x + 3) = false := rfl
```

``zero`` や ``succ`` の代わりに、より馴染みのある表記を使うことができる:

```lean
def sub1 : Nat → Nat
  | 0   => 0
  | x+1 => x

def isZero : Nat → Bool
  | 0   => true
  | x+1 => false
```

加法とゼロ表記には ``[match_pattern]`` 属性が割り当てられているため、これらの表記をパターンマッチングで使うことができる。Leanは、コンストラクタ ``zero`` や ``succ`` が出現するまで、加法やゼロ表記を含む式を単純に正規化する。

パターンマッチングは直積型や ``Option`` 型など、任意の帰納型に対して機能する:

```lean
def swap : α × β → β × α
  | (a, b) => (b, a)

def foo : Nat × Nat → Nat
  | (m, n) => m + n

def bar : Option Nat → Nat
  | some n => n + 1
  | none   => 0
```

パターンマッチングは関数定義だけでなく、場合分けによる証明にも使うことができる:

```lean
namespace Hidden
def not : Bool → Bool
  | true  => false
  | false => true

theorem not_not : ∀ (b : Bool), not (not b) = b
  | true  => rfl  -- proof that not (not true) = true
  | false => rfl  -- proof that not (not false) = false

theorem not_not' : (b : Bool) → not (not b) = b
  | true  => rfl
  | false => rfl
end Hidden
```

パターンマッチングは帰納的に定義された命題を分解するためにも使うことができる:

```lean
example (p q : Prop) : p ∧ q → q ∧ p
  | And.intro h₁ h₂ => And.intro h₂ h₁

example (p q : Prop) : p ∨ q → q ∨ p
  | Or.inl hp => Or.inr hp
  | Or.inr hq => Or.inl hq
```

パターンマッチングは論理的結合子を含む仮説を分解するコンパクトな方法も提供する。

以上の全ての例で、パターンマッチングは「フラットな」場合分けを実行するために使われている。さらに興味深いことに、パターンは次のように入れ子になったコンストラクタを含むこともある。

```lean
def sub2 : Nat → Nat
  | 0   => 0
  | 1   => 0
  | x+2 => x
```

この例において、等式コンパイラはまず入力が ``zero`` か ``succ x`` の形であるかで最初の場合分けを行う。入力が ``zero`` のときは ``0`` を返す。入力が ``succ x`` の形のときは、その ``x`` が ``zero`` か ``succ x`` の形であるかで2回目の場合分けを行う。等式コンパイラは提示されたケースリストから場合分けの方法を決定し、適切な場合分けに失敗したときはエラーを生じる。ここでも、次のように算術の記法を使うことができる。いずれにせよ、関数を定義する等式はdefinitionallyに成立する。

```lean
# def sub2 : Nat → Nat
#   | 0   => 0
#   | 1   => 0
#   | x+2 => x
example : sub2 0 = 0 := rfl
example : sub2 1 = 0 := rfl
example : sub2 (x+2) = x := rfl

example : sub2 5 = 3 := rfl
```

``#print sub2`` と書けば、この関数が再帰子を含むどんな式にコンパイルされたかが分かる。(Leanは ``sub2`` が内部の補助関数 ``sub2.match_1`` を使って定義されていることを伝えるかもしれないが、``#print`` コマンドを使って ``sub2.match_1`` の定義を表示させることもできる。)Leanはこれらの補助関数を使って ``match`` 式をコンパイルする。実際には、上記の定義 ``sub2`` は次のように展開される。

```lean
def sub2 : Nat → Nat :=
  fun x =>
    match x with
    | 0   => 0
    | 1   => 0
    | x+2 => x
```

入れ子になったパターンマッチングの例をさらに挙げる:

```lean
example (p q : α → Prop)
        : (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x)
  | Exists.intro x (Or.inl px) => Or.inl (Exists.intro x px)
  | Exists.intro x (Or.inr qx) => Or.inr (Exists.intro x qx)

def foo : Nat × Nat → Nat
  | (0, n)     => 0
  | (m+1, 0)   => 1
  | (m+1, n+1) => 2
```

等式コンパイラは複数の引数を連続して処理することができる。例えば、一つ上の例 ``foo`` は2つの引数を持つ関数として定義する方が自然だろう:

```lean
def foo : Nat → Nat → Nat
  | 0,   n   => 0
  | m+1, 0   => 1
  | m+1, n+1 => 2
```

別の例を挙げる:

```lean
-- `a :: as` は `cons a as` の糖衣構文

def bar : List Nat → List Nat → Nat
  | [],      []      => 0
  | a :: as, []      => a
  | [],      b :: bs => b
  | a :: as, b :: bs => a + b
```

複数の引数を持つケースは、パターン毎にカンマで区切られることに注意してほしい。

以下の各例では、2番目以降の引数がケースに含まれているが、最初の引数での場合分けのみが行われる。

```lean
# namespace Hidden
def and : Bool → Bool → Bool
  | true,  a => a
  | false, _ => false

def or : Bool → Bool → Bool
  | true,  _ => true
  | false, a => a

def cond : Bool → α → α → α
  | true,  x, y => x
  | false, x, y => y
# end Hidden
```

また、ある引数の値が出力を定義するのに必要ない場合は、その引数のパターンにアンダースコアを使うことができることに注意してほしい。このアンダースコアは*wildcard pattern*(ワイルドカードパターン)あるいは*anonymous variable*(匿名変数)として知られている。等式コンパイラ以外での使い方とは違い、ここでアンダースコアは暗黙の引数を表すものでは**ない**。ワイルドカードにアンダースコアを使うのは関数型プログラミング言語では一般的なので、Leanもその表記を採用した。節[Wildcards and Overlapping Patterns (ワイルドカードとケースの重複)](#wildcards-and-overlapping-patterns-ワイルドカードとケースの重複)ではワイルドカードの概念を拡張し、節[Inaccessible Patterns (アクセス不能パターン)](#inaccessible-patterns-アクセス不能パターン)ではパターン内で暗黙の引数を使用する方法を説明する。

[7章 Inductive Types (帰納型)](./inductive_types.md)で説明したように、帰納データ型はパラメータに依存しうる。次の例では、パターンマッチングを用いて ``tail`` 関数を定義している。引数 ``α : Type u`` は帰納データ型のパラメータであり、パターンマッチングに参加しないことを示すために(関数名・引数リストと型名を区切る)コロンの前に置かれる。Leanは ``:`` の後に帰納型のパラメータが来ることも許可するが、パラメータをパターンマッチさせることはできない。

```lean
def tail1 {α : Type u} : List α → List α
  | []      => []
  | a :: as => as

def tail2 : {α : Type u} → List α → List α
  | α, []      => []
  | α, a :: as => as
```

この2つの例では、パラメータ ``α`` の出現位置が異なるにもかかわらず、どちらの例でも場合分けに参加しないという意味で同じように扱われている。

Leanは、依存型の引数が場合分けにおいて「このケースが生じることはない」という追加の制約を与えるような、より複雑な形のパターンマッチングも扱うことができる。このような*dependent pattern matching*(依存パターンマッチング)の例については、[Dependent Pattern Matching (依存パターンマッチング)](#dependent-pattern-matching-依存パターンマッチング)の節で説明する。

## Wildcards and Overlapping Patterns (ワイルドカードとケースの重複)

前節の例の1つについて考える:

```lean
def foo : Nat → Nat → Nat
  | 0,   n   => 0
  | m+1, 0   => 1
  | m+1, n+1 => 2
```

この例は次のように表現することもできる:

```lean
def foo : Nat → Nat → Nat
  | 0, n => 0
  | m, 0 => 1
  | m, n => 2
```

2つ目の表現では、ケースが重複している。例えば、引数のペア ``0 0`` は3つのケース全てにマッチする。しかし、Leanは上のケースから順にパターンマッチングを試し、一番最初にマッチしたケースを使うことで曖昧さを解消するので、この2つの例は結果的に同じ関数を定義している。実際、2つ目の表現について以下の等式がdefinitionallyに成立する:

```lean
def foo : Nat → Nat → Nat
  | 0, n => 0
  | m, 0 => 1
  | m, n => 2
example : foo 0     0     = 0 := rfl
example : foo 0     (n+1) = 0 := rfl
example : foo (m+1) 0     = 1 := rfl
example : foo (m+1) (n+1) = 2 := rfl
```

``m`` と ``n`` の値は出力の定義に必要ないので、代わりにワイルドカードパターンを使ってもよい。

```lean
def foo : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 1
  | _, _ => 2
```

直前の定義と同様に、この ``foo`` の定義が4つの恒等式をdefinitionallyに満たすことは容易に確認できる。

関数型プログラミング言語の中には、*incomplete pattern matching*(不完全なパターンマッチング)をサポートするものがある。これらの言語では、インタプリタはケースリスト内のどのケースともマッチしない入力に対して例外を生成するか、任意の値を返す。Leanでは、``Inhabited`` 型クラスを使うと、「どのケースともマッチしない入力に対して任意の値を返す」アプローチをシミュレートできる。大雑把に言うと、``Inhabited α`` は ``α`` の要素が存在することの証人である。[10章 Type Classes (型クラス)](./type_classes.md)では、Leanに適切な基底型がinhabited(有項)であることを指示でき、Leanはその指示に基づいて、他の構築された型が有項であることを自動的に推論できることを説明する。これに基づいて、標準ライブラリは任意の有項型のデフォルト項 ``default`` を提供する。

型 ``Option α`` を使って不完全なパターンマッチングをシミュレートすることもできる。このアプローチでは、入力が適切に提供されたケースとマッチしたときは ``some a`` を返し、不完全なケースとマッチしたときは ``none`` を返す。次の例は、両方のアプローチを示している。

```lean
def f1 : Nat → Nat → Nat
  | 0, _  => 1
  | _, 0  => 2
  | _, _  => default  -- the "incomplete" case

example : f1 0     0     = 1       := rfl
example : f1 0     (a+1) = 1       := rfl
example : f1 (a+1) 0     = 2       := rfl
example : f1 (a+1) (b+1) = default := rfl

def f2 : Nat → Nat → Option Nat
  | 0, _  => some 1
  | _, 0  => some 2
  | _, _  => none     -- the "incomplete" case

example : f2 0     0     = some 1 := rfl
example : f2 0     (a+1) = some 1 := rfl
example : f2 (a+1) 0     = some 2 := rfl
example : f2 (a+1) (b+1) = none   := rfl
```

等式コンパイラは賢い。以下の定義のどれかのケースを省くと、エラーメッセージでどんなケースがカバーされていないかを知らせてくれる。

```lean
def bar : Nat → List Nat → Bool → Nat
  | 0,   _,      false => 0
  | 0,   b :: _, _     => b
  | 0,   [],     true  => 7
  | a+1, [],     false => a
  | a+1, [],     true  => a + 1
  | a+1, b :: _, _     => a + b
```

また、等式コンパイラは適切な状況では ``casesOn`` の代わりに "if ... then ... else" 構文を用いる。

```lean
def foo : Char → Nat
  | 'A' => 1
  | 'B' => 2
  | _   => 3

#print foo.match_1
```

## Structural Recursion and Induction (構造的再帰と構造的帰納法)

再帰的定義もサポートしていることが、等式コンパイラを強力なものにしている。次の3つの節では、ここに挙げる3つの概念それぞれについて説明する:

- structurally recursive definitions(構造的再帰的定義)
- well-founded recursive definitions(整礎再帰的定義)
- mutually recursive definitions(相互再帰的定義)

一般的に、等式コンパイラは次の形式の入力を処理する:

```
def foo (a : α) : (b : β) → γ
  | [patterns₁] => t₁
  ...
  | [patternsₙ] => tₙ
```

ここで、``(a : α)`` はパラメータの列、``(b : β)`` はパターンマッチングが行われる引数の列、``γ`` は任意の型であり、``γ`` は ``a`` と ``b`` に依存することができる。``[patterns₁]`` から ``[patternsₙ]`` は同じ数のパターンを含むべきであり、1つのパターンが ``β`` の各要素と対応する。これまで見てきたように、パターンは変数、他のパターンにコンストラクタを適用したもの、またはそのような形式に正規化される式のいずれかである(ここで、コンストラクタでないものは ``[match_pattern]`` 属性でマークされる)。コンストラクタの出現はケースの分割を促す。ここで、コンストラクタへの引数は与えられた変数で表される。節[Dependent Pattern Matching (依存パターンマッチング)](#dependent-pattern-matching-依存パターンマッチング)では、パターンマッチングでは何の役割も果たさないが、式の型チェックを行うために必要となる明示的な項をパターンに含める必要がある場合があることを説明する。この明示的な項は今述べた理由により*inaccessible patterns*(アクセス不能パターン)と呼ばれる。しかし、節[Dependent Pattern Matching (依存パターンマッチング)](#dependent-pattern-matching-依存パターンマッチング)より前では、アクセス不能パターンを使う必要はない。

前節で見たように、出力を定義する項 ``t₁, ..., tₙ`` は、任意のパラメータ ``a`` だけでなく、対応するパターン内で導入された変数を利用することができる。再帰と帰納が可能なのは、出力を定義する項が ``foo`` への再帰的呼び出しを含むことすら可能だからである。この節では、*structural recursion*(構造的再帰)を扱う。構造的再帰では、``=>`` の右辺に現れる ``foo`` への引数は ``=>`` の左辺のパターンの部分項である。これは、部分項はマッチした引数よりstructurally small(構造的に小さい)であるため、帰納型の項としてマッチした引数より先に構築されるという考え方である。前章の構造的再帰の例を、今度は等式コンパイラを使って定義しよう:

```lean
open Nat
def add : Nat → Nat → Nat
  | m, zero   => m
  | m, succ n => succ (add m n)

theorem add_zero (m : Nat)   : add m zero = m := rfl
theorem add_succ (m n : Nat) : add m (succ n) = succ (add m n) := rfl

theorem zero_add : ∀ n, add zero n = n
  | zero   => rfl
  | succ n => congrArg succ (zero_add n)

def mul : Nat → Nat → Nat
  | n, zero   => zero
  | n, succ m => add (mul n m) n

theorem mul_zero (m : Nat)   : mul m zero = zero := rfl
theorem mul_succ (m n : Nat) : mul m (succ n) = add (mul m n) m := rfl
```

この ``zero_add`` の証明は、Leanにおいて帰納法による証明が再帰の一つの形であることを明らかにしている。

上の例は、``add`` と ``mul`` を定義する式がdefinitionallyに成立することを示している。等式コンパイラは構造的帰納法による証明内でも、可能な限り関数を定義する式がdefinitionallyに成立するようにする。例えば、``zero_add`` の証明において、引数が ``zero`` のケースは ``rfl`` を使うだけで示せる。しかしながら、他の状況では、引数の部分項に関する当該定理(例えば ``zero_add n``)は*propositionally*にしか成立しない。つまり、これは明示的に適用されなければならない等式定理である。等式コンパイラは ``zero_add n`` のような定理を内部的に作成するが、これらの定理はユーザーが直接使うものではなく、``simp`` タクティクが必要に応じて使うように設定されている。したがって、次の ``zero_add`` の証明も機能する:

```lean
open Nat
# def add : Nat → Nat → Nat
#   | m, zero   => m
#   | m, succ n => succ (add m n)
theorem zero_add : ∀ n, add zero n = n
  | zero   => by simp [add]
  | succ n => by simp [add, zero_add]
```

パターンマッチングによる定義と同様に、構造的再帰や構造的帰納法のパラメータがコロンの前に現れることがある。このようなパラメータは、定義が処理される前にローカルコンテキストに追加される。例えば、加法の定義は次のように書くこともできる:

```lean
open Nat
def add (m : Nat) : Nat → Nat
  | zero   => m
  | succ n => succ (add m n)
```

この例を ``match`` を使って書くこともできる。

```lean

/- `match` を使う場合はもちろん `:=` が必要になる -/

open Nat
def add (m n : Nat) : Nat :=
  match n with
  | zero   => m
  | succ n => succ (add m n)
```

構造的再帰のもっと面白い例はフィボナッチ関数 ``fib`` である。

```lean
def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

example : fib 0 = 1 := rfl
example : fib 1 = 1 := rfl
example : fib (n + 2) = fib (n + 1) + fib n := rfl

example : fib 7 = 21 := rfl
```

ここで、``n + 2``( ``succ (succ n)`` とdefinitionally equal)における ``fib`` 関数の値は、``n + 1``( ``succ n`` とdefinitionally equal)における値と ``n`` における値で定義される。しかし、これはフィボナッチ関数を計算する方法としてはきわめて非効率的で、実行時間は指数 ``n`` の指数関数となる。もっと良い方法がある:

```lean
def fibFast (n : Nat) : Nat :=
  (loop n).2
where
  loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)

#eval fibFast 100
```

``where`` の代わりに ``let rec`` を用いた定義は次の通り:

```lean
def fibFast (n : Nat) : Nat :=
  let rec loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)
  (loop n).2
```

どちらの例でも、Leanは補助関数 ``fibFast.loop`` を生成する。

構造的再帰を処理するために、等式コンパイラは各帰納型の定義時に自動生成される定数 ``below`` と ``brecOn`` を用いて、*course-of-values recursion*(累積再帰)を使用する。``Nat.below`` と ``Nat.brecOn`` の型を見れば、それらがどのように機能するかを知ることができる:

```lean
variable (C : Nat → Type u)

#check (@Nat.below C : Nat → Type u)

#reduce @Nat.below C (3 : Nat)

#check (@Nat.brecOn C : (n : Nat) → ((n : Nat) → @Nat.below C n → C n) → C n)
```

型 ``@Nat.below C (3 : nat)`` は、``C 0``、``C 1``、``C 2`` の項を格納するデータ構造である。累積再帰は ``Nat.brecOn`` によって実装される。``Nat.brecOn`` は型 ``(n : Nat) → C n`` を持つ依存関数の入力 ``m`` における値を、(``@Nat.below C m`` の要素として表される)その関数の以前の全ての値を使って定義することを可能にする。

累積再帰の利用は、等式コンパイラがLeanのカーネルに対して特定の関数が停止することを正当に主張するために使うテクニックの一つである。他の関数型プログラミング言語のコンパイラと同様、再帰関数をコンパイルするコードジェネレータに影響を与えることはない。``#eval fib n`` の実行時間は指数 ``n`` の指数関数となることを思い出してほしい。一方で、``#reduce fib n`` は ``brecOn`` による構築に基づいた定義を使用するため効率的である。

```lean
def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

-- #eval fib 50 -- slow
#reduce fib 50  -- fast

#print fib
```

再帰的定義のもう一つの良い例がリストの ``append`` 関数である。

```lean
def append : List α → List α → List α
  | [],    bs => bs
  | a::as, bs => a :: append as bs

example : append [1, 2, 3] [4, 5] = [1, 2, 3, 4, 5] := rfl
```

もう一つ例を挙げる: ``listAdd x y`` は2つのリストのどちらかの要素がなくなるまで、最初のリストの先頭の要素 ``a`` と2番目のリストの先頭の要素 ``b`` を削除して ``a + b`` をリスト ``z`` に追加する操作を繰り返し、最後に ``z`` を返す。

```lean
def listAdd [Add α] : List α → List α → List α
  | [],      _       => []
  | _,       []      => []
  | a :: as, b :: bs => (a + b) :: listAdd as bs

#eval listAdd [1, 2, 3] [4, 5, 6, 6, 9, 10]
-- [5, 7, 9]
```

以下の練習問題で、これに似た例に関して実験してみることをお勧めする。

## Local Recursive Declarations (ローカルな再帰的定義)

``let rec`` キーワードを使うと、ローカルな再帰的定義を宣言することができる。

```lean
def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)
  loop n []

#check @replicate.loop
-- {α : Type} → α → Nat → List α → List α
```

Leanは各 ``let rec`` に対して補助定義を作成する。上の例では、``replicate`` の定義内にある ``let rec loop`` のために ``replicate.loop`` の定義を作成している。Leanは、``let rec`` 宣言内で使われたローカル変数を定義中の関数のパラメータに追加することで、宣言を「閉じる」ことに注意してほしい。例えば、ローカル変数 ``a`` は ``let rec loop`` 内で使われている。

``let rec`` をタクティクモード内で使うこともできる。また、帰納法による証明を作るために ``let rec`` を使うこともできる。

```lean
# def replicate (n : Nat) (a : α) : List α :=
#  let rec loop : Nat → List α → List α
#    | 0,   as => as
#    | n+1, as => loop n (a::as)
#  loop n []
theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  let rec aux (n : Nat) (as : List α)
              : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp [replicate.loop, aux n, Nat.add_succ, Nat.succ_add]
  exact aux n []
```

定義を記述した後に ``where`` キーワードを使って補助再帰的定義を導入することもできる。Leanはこれらを ``let rec`` に変換する。

```lean
def replicate (n : Nat) (a : α) : List α :=
  loop n []
where
  loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)

theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  exact aux n []
where
  aux (n : Nat) (as : List α)
      : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp [replicate.loop, aux n, Nat.add_succ, Nat.succ_add]
```

## Well-Founded Recursion and Induction (整礎再帰と整礎帰納法)

構造的再帰が使えない場合は、整礎再帰を使えば再帰的定義中の関数が停止することを証明できる。整礎再帰に必要なのは、整礎関係と、各再帰適用(``f t`` の形をとる)が特定の項 ``t`` をこの関係において「減少させる」ことの証明である。依存型理論は整礎再帰を表現し、その正当性を証明するのに十分強力である。これらの仕組みを理解するために必要な論理的背景の説明から始めよう。

Leanの標準ライブラリは2つの述語 ``Acc r a`` と ``WellFounded r`` を定義している。ここで、``r`` は型 ``α`` 上の二項関係であり、``a`` は型 ``α`` の要素である。

```lean
variable (α : Sort u)
variable (r : α → α → Prop)

#check (Acc r : α → Prop)
#check (WellFounded r : Prop)
```

1つ目 ``Acc`` は帰納的に定義された述語である。定義(唯一のコンストラクタ ``Acc.intro``)によると、``Acc r x`` は ``∀ y, r y x → Acc r y`` と同値である。``Acc r x`` は ``r`` の下で ``x`` がアクセス可能であることを意味する。``r y x`` が一種の順序関係 ``y ≺ x`` を表すと考えるなら、``Acc r x`` は ``x`` の全ての前者がアクセス可能であることと同値である。特に、``x`` が前者を持たない場合、``x`` はアクセス可能である。任意の型 ``α`` の任意のアクセス可能な項 ``x`` に対して、``x`` の全ての前者に先に値を割り当てることで、``x`` にも値を割り当てることができるはずである。

```lean
noncomputable def f {α : Sort u}
      (r : α → α → Prop)
      (h : WellFounded r)
      (C : α → Sort v)
      (F : (x : α) → ((y : α) → r y x → C y) → C x)
      : (x : α) → C x := WellFounded.fix h F
```

``f`` の引数が長い列をなしているが、前半はすでに見たとおりである: ``α`` は型、``r`` は二項関係、そして ``h`` は「``r`` が整礎である」という仮説である。変数 ``C`` は再帰的定義の動機を表す: 各項 ``x : α`` について、``C x`` の項を構築したい。関数 ``F`` は ``C x`` の項を構築するための帰納的レシピを提供する: ``F`` は ``x`` の各前者 ``y`` について ``C y`` の項が与えられたとき、要素 ``C x`` を構築する方法を教えてくれる。

``WellFounded.fix`` は帰納法においても同様に機能する。つまり、もし ``≺`` が整礎で、``∀ x, C x`` を証明したいなら、任意の ``x`` に対して「``∀ y ≺ x, C y`` ならば ``C x``」を示せば十分である。

上の例では、コードジェネレータが現在 ``WellFounded.fix`` をサポートしていないため、``noncomputable`` という修飾子を使用している。関数 ``WellFounded.fix`` はLeanが関数の停止を正当に主張するために使う(累積再帰とは別の)ツールである。

Leanは、自然数に関する通常の順序 ``<`` が整礎であることを知っている。また、Leanは既存の順序から新しい整礎順序を構築する方法もいくつか知っている。例えば、辞書式順序を使う方法がある。

以下は、標準ライブラリ内にある自然数の除法の定義である。

```lean
open Nat

theorem div_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun h => sub_lt (Nat.lt_of_lt_of_le h.left h.right) h.left

def div.F (x : Nat) (f : (x₁ : Nat) → x₁ < x → Nat → Nat) (y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    (f (x - y) (div_lemma h) y) + 1
  else
    zero

noncomputable def div := WellFounded.fix (measure id).wf div.F

#reduce div 8 2 -- 4
```

この定義はやや分かりにくい。ここで再帰は ``x`` に対して行われ、``div.F x f : Nat → Nat`` はその固定された ``x`` に対する「``y`` で割る」関数を返す。再帰のレシピである ``div.F`` の第2引数 ``f`` は、``x`` より小さい全ての値 ``x₁`` に対して「``y`` で割る」関数を返す(と想定される)関数であることを理解する必要がある。

elaboratorはこのような定義をより便利に作成できるようにデザインされている。次のような定義の書き方が認められる:

```lean
def div (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    have : x - y < x := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
    (div (x - y) y) + 1
  else
    0
```

再帰的な定義に遭遇すると、Leanはまず構造的再帰を試み、それが失敗したときだけ整礎再帰を試みる。Leanは ``decreasing_tactic`` というタクティクを使って、再帰適用後の項が元の項より「小さい」ことを示す。上の例の補助命題 ``x - y < x`` はこのタクティクのためのヒントとみなされる。

``div`` を定義する等式はdefinitionallyに成立**しない**。しかし、``unfold`` タクティクを使えば ``div`` を展開することはできる。[``conv``](./conv.md)を使うと、展開したい ``div`` 適用後の項を選択できる。

```lean
# def div (x y : Nat) : Nat :=
#  if h : 0 < y ∧ y ≤ x then
#    have : x - y < x := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
#    div (x - y) y + 1
#  else
#    0
example (x y : Nat) : div x y = if 0 < y ∧ y ≤ x then div (x - y) y + 1 else 0 := by
  conv => lhs; unfold div -- 等式の左辺の `div` を展開する

example (x y : Nat) (h : 0 < y ∧ y ≤ x) : div x y = div (x - y) y + 1 := by
  conv => lhs; unfold div
  simp [h]
```

次の例も同様の構文を使って整礎再帰を行う: ``natToBin`` は任意の自然数を0と1のリストとして表される2進表記に変換する。まず、再帰適用後の項が元の項より減少する証拠を示さなければならないが、これは ``sorry`` で行う。``sorry`` はインタプリタが関数を正常に評価することを妨げるものではない。(訳者注: ``#eval`` を使って関数を評価するだけなら証拠は不要ということだと思われる。しかし証拠がない場合、任意の引数 ``n`` に対して ``#eval natToBin n`` が停止する保証はないと思われる。)

```lean
def natToBin : Nat → List Nat
  | 0     => [0]
  | 1     => [1]
  | n + 2 =>
    have : (n + 2) / 2 < n + 2 := sorry
    natToBin ((n + 2) / 2) ++ [n % 2]

#eval natToBin 1234567
```

最後の例として、Leanではアッカーマン関数が本来の定義をそのまま書くだけで定義できることを見る。なぜなら、この整礎再帰は自然数の辞書式順序の整礎性によって正当化されるからである。``termination_by`` キーワードはLeanに辞書式順序を使うように指示している。実際には、このキーワードは関数の2つの引数を ``Nat × Nat`` 型の項にマッピングしている。そして、Leanは型クラス解決を使って ``WellFoundedRelation (Nat × Nat)`` 型の要素を合成する。

```lean
def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by x y => (x, y)

#eval ack 3 5
-- アッカーマン関数は入力値の増加に伴い出力値が急速に増加する関数であり、
-- 例えば `#eval ack 4 1` などはバッファオーバーフロー等のエラーを引き起こす可能性が高いため、
-- 実行しないことをお勧めする。
```

インスタンス ``WellFoundedRelation (α × β)`` が辞書式順序を使うため、上の定義の中では辞書式順序が使われていることに注意してほしい。また、Leanは標準ライブラリ内で次のインスタンス ``instWellFoundedRelation`` も定義している。

```lean
instance (priority := low) [SizeOf α] : WellFoundedRelation α :=
  sizeOfWFRel
```

次の例では、``as.size - i`` が再帰適用によって減少することを示すことで、``go`` の停止性を証明する。

```lean
-- Array `as` を先頭から見て、
-- `as` の要素 `a` が `p a` を満たす限りArray `r` に `a` を追加し、`r` を返す関数
def takeWhile (p : α → Bool) (as : Array α) : Array α :=
  go 0 #[]
where
  go (i : Nat) (r : Array α) : Array α :=
    if h : i < as.size then
      let a := as.get ⟨i, h⟩
      if p a then
        go (i+1) (r.push a)
      else
        r
    else
      r
termination_by as.size - i

#eval takeWhile (fun n : Nat => if n % 2 = 1 then true else false) #[1, 3, 5, 6, 7]
```

この例では、補助関数 ``go`` は再帰的だが、``takeWhile`` は再帰的でないことに注意してほしい。

デフォルトでは、Leanは ``decreasing_tactic`` タクティクを使って再帰適用後の項が元の項より小さいことを証明する。``decreasing_by`` 修飾子を使うと、独自のタクティクを提供することができる。以下はその例である。

```lean
theorem div_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun ⟨ypos, ylex⟩ => Nat.sub_lt (Nat.lt_of_lt_of_le ypos ylex) ypos

def div (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    div (x - y) y + 1
  else
    0
decreasing_by apply div_lemma; assumption
```

``decreasing_by`` は ``termination_by`` を置き換えるものではなく、互いに補完し合うものである。``termination_by`` は整礎関係を指定するのに使われ、``decreasing_by`` は再帰適用後の項が元の項より小さいことを示すために独自のタクティクを提供するために使われる。次の例ではその両方を使う。

```lean
def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by x y => (x, y)
decreasing_by
  all_goals simp_wf -- unfolds well-founded recursion auxiliary definitions
  · apply Prod.Lex.left; simp_arith
  · apply Prod.Lex.right; simp_arith
  · apply Prod.Lex.left; simp_arith
```

``decreasing_by sorry`` を使えば、Leanに関数が停止することを「信じ」させることができる。

```lean
def natToBin : Nat → List Nat
  | 0     => [0]
  | 1     => [1]
  | n + 2 => natToBin ((n + 2) / 2) ++ [n % 2]
decreasing_by sorry

#eval natToBin 1234567
```

``sorry`` を使うことは新しい公理を導入することと同じであり、避けるべきであることを思い出してほしい。次の例では、``sorry`` を使って ``False`` を証明した。コマンド ``#print axioms`` は、``unsound`` が ``sorry`` を実装するために使われている不健全な公理 ``sorryAx`` に依存していることを示す。

```lean
def unsound (x : Nat) : False :=
  unsound (x + 1)
decreasing_by sorry

#check unsound 0
-- `unsound 0` is a proof of `False`

#print axioms unsound
-- 'unsound' depends on axioms: [sorryAx]
```

要約:

- ``termination_by`` がない場合、Leanはある引数を選択し、型クラス解決を使って選択した引数の型上の整礎関係を合成することで、(可能であれば)整礎関係が導出される。

- ``termination_by`` が指定されている場合、``termination_by`` は関数の引数を ``α`` 型にマッピングし、再び型クラス解決が使われる。``β × γ`` に関するデフォルトインスタンスは ``β`` と ``γ`` 上の整礎関係に基づいた辞書式順序であることを思い出してほしい。

- ``Nat`` に関するデフォルトの整礎関係インスタンスは ``<`` である。

- デフォルトでは、選択された整礎関係について、再帰適用後の項が元の項より小さいことを示すために ``decreasing_tactic`` タクティクが使われる。``decreasing_tactic`` が失敗した場合に表示されるエラーメッセージは残りのゴール ``... |- G`` を含む。``decreasing_tactic`` は ``assumption`` タクティクを使うことに注意。つまり、``have`` 式を使ってコンテキストに仮説を追加することがターゲット ``G`` の証明の役に立つことがある。``decreasing_by`` を使って独自のタクティクを提供することもできる。

## Mutual Recursion (相互再帰)

Leanは*mutual recursive definitions*(相互再帰的定義)もサポートしている。その構文は相互帰納型と似ている。以下に例を挙げる:

```lean
mutual
  def even : Nat → Bool
    | 0   => true
    | n+1 => odd n

  def odd : Nat → Bool
    | 0   => false
    | n+1 => even n
end

example : even (a + 1) = odd a := by
  simp [even]

example : odd (a + 1) = even a := by
  simp [odd]

theorem even_eq_not_odd : ∀ a, even a = not (odd a) := by
  intro a; induction a
  . simp [even, odd]
  . simp [even, odd, *]
```

``even`` は ``odd`` を用いて定義され、``odd`` は ``even`` を用いて定義されているため、この定義は相互定義になっている。内部では、この定義は単一の再帰的定義としてコンパイルされる。内部で定義された関数は、直和型の項を引数として取る。直和型の項の片側は ``even`` への入力、もう片側は ``odd`` への入力と解釈される。そして、入力に適した出力を返す。この関数を定義するために、Leanは適切な整礎関係を使用するが、その内部はユーザーから隠されている。このような定義を利用する正規の方法は、前節でやったように ``simp`` または ``unfold`` を使うことである。

また、相互再帰的定義は相互帰納型および入れ子帰納型を扱う自然な方法を提供する。前章で示した、相互帰納述語型としての ``Even`` と ``Odd`` の定義を思い出してほしい。

```lean
mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : ∀ n, Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : ∀ n, Even n → Odd (n + 1)
end
```

コンストラクタ ``even_zero``、``even_succ``、``odd_succ`` はある自然数が偶数か奇数かを示す積極的な手段を提供する。0が奇数でないこと、そして後の2つのコンストラクタの意味が逆であることを知るには、この相互帰納型がこれらのコンストラクタによって生成されたという事実を使う必要がある。いつものように、コンストラクタは定義された型の名前を持つ名前空間に保管されており、コマンド ``open Even Odd`` を使えば、コンストラクタに便利にアクセスできるようになる。

```lean
# mutual
#  inductive Even : Nat → Prop where
#    | even_zero : Even 0
#    | even_succ : ∀ n, Odd n → Even (n + 1)
#  inductive Odd : Nat → Prop where
#    | odd_succ : ∀ n, Even n → Odd (n + 1)
# end
open Even Odd

theorem not_odd_zero : ¬ Odd 0 :=
  fun h => nomatch h

theorem even_of_odd_succ : ∀ n, Odd (n + 1) → Even n
  | _, odd_succ n h => h

theorem odd_of_even_succ : ∀ n, Even (n + 1) → Odd n
  | _, even_succ n h => h
```

別の例を挙げる。入れ子帰納型を使って、型 ``Term`` の項を帰納的に定義することを考える。ここで、``Term`` の項は定数(文字列によって与えられる名前を持つ)か、定数のリストに定数を適用した結果のどちらかになるとする。

```lean
inductive Term where
  | const : String → Term
  | app   : String → List Term → Term
```

そして、相互再帰を使って、各項の中に登場する定数の数を数える関数と、項のリストの中に登場する要素の数を数える関数を定義することができる。

```lean
# inductive Term where
#  | const : String → Term
#  | app   : String → List Term → Term
namespace Term

mutual
  def numConsts : Term → Nat
    | const _ => 1
    | app _ cs => numConstsLst cs

  def numConstsLst : List Term → Nat
    | [] => 0
    | c :: cs => numConsts c + numConstsLst cs
end

def sample := app "f" [app "g" [const "x"], const "y"]
def sample2 := [app "g" [const "x", const "y"], const "y"]

#eval numConsts sample
#eval numConstsLst sample2

end Term
```

最後の例として、項 ``e`` 内の定数 ``a`` を ``b`` に置き換える関数 ``replaceConst a b e`` を定義し、``e`` が持つ定数の個数と ``replaceConst a b e`` が持つ定数の個数が同じであることを証明する。この証明は、相互帰納法を使っていることに注意してほしい。

```lean
# inductive Term where
#  | const : String → Term
#  | app   : String → List Term → Term
# namespace Term
# mutual
#  def numConsts : Term → Nat
#    | const _ => 1
#    | app _ cs => numConstsLst cs
#   def numConstsLst : List Term → Nat
#    | [] => 0
#    | c :: cs => numConsts c + numConstsLst cs
# end
mutual
  def replaceConst (a b : String) : Term → Term
    | const c => if a == c then const b else const c
    | app f cs => app f (replaceConstLst a b cs)

  def replaceConstLst (a b : String) : List Term → List Term
    | [] => []
    | c :: cs => replaceConst a b c :: replaceConstLst a b cs
end

mutual
  theorem numConsts_replaceConst (a b : String) (e : Term)
            : numConsts (replaceConst a b e) = numConsts e := by
    match e with
    | const c => simp [replaceConst]; split <;> simp [numConsts]
    | app f cs => simp [replaceConst, numConsts, numConsts_replaceConstLst a b cs]

  theorem numConsts_replaceConstLst (a b : String) (es : List Term)
            : numConstsLst (replaceConstLst a b es) = numConstsLst es := by
    match es with
    | [] => simp [replaceConstLst, numConstsLst]
    | c :: cs =>
      simp [replaceConstLst, numConstsLst, numConsts_replaceConst a b c,
            numConsts_replaceConstLst a b cs]
end
```

## Dependent Pattern Matching (依存パターンマッチング)

[Pattern Matching (パターンマッチング)](#pattern-matching-パターンマッチング)の節で説明した全ての例は、``casesOn`` と ``recOn`` を使って簡単に書くことができる。しかし、``Vector α n`` のような添字付き帰納族では、ケース分割が添字の値に制約を課すため、簡単に書けないことがよくある。もし等式コンパイラが無かったら、再帰子だけを使って ``map``、``zip``、``unzip`` などの非常に単純な関数を定義するために、多くの定型的なコードが必要になっただろう。その難しさを理解するために、ベクトル ``v : Vector α (succ n)`` を受け取り、最初の要素を削除したベクトルを返す関数 ``tail`` を定義するためには何が必要かを考えてみよう。まずは、``casesOn`` 関数を使うことが考えられる:

```lean
inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

namespace Vector

#check @Vector.casesOn
/-
  {α : Type u}
  → {motive : (a : Nat) → Vector α a → Sort v} →
  → {a : Nat} → (t : Vector α a)
  → motive 0 nil
  → ((a : α) → {n : Nat} → (a_1 : Vector α n) → motive (n + 1) (cons a a_1))
  → motive a t
-/

end Vector
```

しかし、入力が ``nil`` の場合は何を返せばいいだろうか。何かおかしなことが起こっている: ``v`` の型が ``Vector α (succ n)`` なら、``v`` が ``nil`` である**はずがない**。しかし、それを ``casesOn`` に伝える方法は明らかではない。

1つの解決策は、補助関数を定義することである:

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def tailAux (v : Vector α m) : m = n + 1 → Vector α n :=
  Vector.casesOn (motive := fun x _ => x = n + 1 → Vector α n) v
    (fun h : 0 = n + 1 => Nat.noConfusion h)
    (fun (a : α) (m : Nat) (as : Vector α m) =>
     fun (h : m + 1 = n + 1) =>
       Nat.noConfusion h (fun h1 : m = n => h1 ▸ as))

def tail (v : Vector α (n+1)) : Vector α n :=
  tailAux v rfl
# end Vector
```

補助関数 ``tailAux`` において、``v`` が ``nil`` の場合、``m`` の値は ``0`` に決定し、``noConfusion`` は ``0 = succ n`` は成立しえないという事実を使う。そうでなければ、``v`` は ``a :: w`` の形をとり、``w`` を長さ ``m`` のベクトルから長さ ``n`` のベクトルへキャストした後、単純に ``w`` を返すことができる(``h1 ▸ as``)。

``tail`` を定義する上で難しいのは、添字間の関係を維持することである。``tailAux`` 内の仮説 ``e : m = n + 1`` は、``n`` と小前提(``Vector.casesOn`` の4番目と5番目の引数)に関連した添字(``0`` と ``m + 1``)の関係を ``noConfusion`` 等に伝えるために使われる。さらに、``zero = n + 1`` のケースは到達不能である。このようなケースを破棄する正規の方法は ``noConfusion`` を使うことである。

しかし、実際は ``tail`` 関数は再帰を使って簡単に定義できる。そして、等式コンパイラが全ての定型コードを自動的に生成してくれる。似た例をいくつか紹介しよう:

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def head : {n : Nat} → Vector α (n+1) → α
  | n, cons a as => a

def tail : {n : Nat} → Vector α (n+1) → Vector α n
  | n, cons a as => as

theorem eta : ∀ {n : Nat} (v : Vector α (n+1)), cons (head v) (tail v) = v
  | n, cons a as => rfl

def map (f : α → β → γ) : {n : Nat} → Vector α n → Vector β n → Vector γ n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (f a b) (map f as bs)

def zip : {n : Nat} → Vector α n → Vector β n → Vector (α × β) n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (a, b) (zip as bs)
# end Vector
```

再帰的定義において、``head nil`` のような「到達不能」なケースはケースリストから除外できることに注意してほしい。自動生成される添字付き帰納族の定義は単純とは言いがたいものである。次の例について、``#print`` コマンドの出力を見てほしい:

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def map (f : α → β → γ) : {n : Nat} → Vector α n → Vector β n → Vector γ n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (f a b) (map f as bs)

#print map
#print map.match_1
# end Vector
```

``map`` 関数を手で定義するのは ``tail`` 関数よりもさらに面倒である。自信のある人は ``recOn``、``casesOn``、``noConfusion`` を使って ``map`` 関数を手作りしてみてほしい。

## Inaccessible Patterns (アクセス不能パターン)

依存パターンマッチングにおいて、項の型を適切に特殊化するために、定義には必要のない引数を含まなければならない場合がある。Leanでは、このような補助項を、パターンマッチングにおいて*inaccessible*(アクセス不能)なものとしてマークすることができる。例えば、左辺に出現する項が変数単体でも変数にコンストラクタを適用したものでもない場合、これらの注釈は不可欠である。なぜなら、それらの項はパターンマッチングにおいて不適切なターゲットだからである。このようなアクセス不能パターンは、ケースの左辺の*don't care*な構成要素とみなすことができる。``.(t)`` と書くことで、補助項へのアクセスが不能であることを宣言することができる。アクセス不能パターンの形が推論できる場合は、``_`` と書いてもよい。

次の例では、「``f`` のimage(像)の中にある」という性質を定義する帰納型を宣言する。型 ``ImageOf f b`` の項は、``b`` が ``f`` の像の中にあることの証拠だと見なすことができる。コンストラクタ ``imf`` はそのような証拠を構築するために使われる。それから、``f`` の像の中にある項 ``b`` を受け取り、証拠 ``imf a`` に基づいて、``f`` によって ``b`` にマップされた要素の1つ ``a`` を返す「逆関数」を持つ関数 ``f`` を定義することができる。型付けのルールに従うと、最初の引数を ``f a`` と書かなければならないが、この項は変数単体でも変数にコンストラクタを適用したものでもないため、パターンマッチングを用いた定義において何の役割も果たさない。以下の逆関数 ``inverse`` を定義するためには、``f a`` にアクセス不能であるとマーク**しなければならない**。

```lean
inductive ImageOf {α β : Type u} (f : α → β) : β → Type u where
  | imf : (a : α) → ImageOf f (f a)

open ImageOf

/-
def bad_inverse {f : α → β} : (b : β) → ImageOf f b → α
  | b, imf a => a  -- `imf a` has type `ImageOf f (f a)` but is expected to have type `ImageOf f b`

def bad_inverse' {f : α → β} : (b : β) → ImageOf f b → α
  | f a, imf a => a  -- invalid pattern
-/

def inverse {f : α → β} : (b : β) → ImageOf f b → α
  | .(f a), imf a => a

def inverse' {f : α → β} : (b : β) → ImageOf f b → α
  | _, imf a => a
```

上記の例では、アクセス不能注釈は ``f`` がパターンマッチング対象の変数では**ない**ことを明確にしている。

アクセス不能パターンは、依存パターンマッチングを利用する定義を明確にし、制御するために使用することができる。ある型 ``α`` に関連する加法演算があると仮定して、``α`` の項を要素に持つ2つのベクトルを足し合わせる関数 ``Vector.add`` を定義することを考えてみよう:

```lean
inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

namespace Vector

def add [Add α] : {n : Nat} → Vector α n → Vector α n → Vector α n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (a + b) (add as bs)

end Vector
```

引数 ``{n : Nat}`` はコロンの後に現れるが、これはパターンマッチングを用いた定義内で ``n`` を固定し続けることができないからである。この定義を実装したとき、等式コンパイラは最初の引数が ``0`` か ``n+1`` の形をとるかのケース判別から始める。続いて、次の2つの引数についてネストされたケース判別がなされる。それぞれのケースについて、等式コンパイラは最初の引数 ``n`` のパターンと整合性のないケースを除外する(例えば、``n+1, nil, nil`` というパターンたちを持つケースを除外する)。

しかし、実際には最初の引数 ``n`` についてケース判別をする必要はない。``Vector`` の ``casesOn`` エリミネータは2番目の引数でケース判別をするときに、引数 ``n`` の値を自動的に抽象化して ``0`` か ``n + 1`` に置き換える。アクセス不能パターンを使うことで、等式コンパイラに ``n`` でのケース判別を避けるように促すことができる。

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def add [Add α] : {n : Nat} → Vector α n → Vector α n → Vector α n
  | .(_), nil,       nil       => nil
  | .(_), cons a as, cons b bs => cons (a + b) (add as bs)
# end Vector
```

この位置をアクセス不能パターンとしてマークすることは、等式コンパイラに次の2つのことを伝える。第一に、最初の引数の形式は他の引数によってもたらされる制約から推論されるべきである。第二に、最初の引数はパターンマッチングに参加すべきでは**ない**。

アクセス不能パターン ``.(_)`` は簡便のため ``_`` と書くことができる。

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def add [Add α] : {n : Nat} → Vector α n → Vector α n → Vector α n
  | _, nil,       nil       => nil
  | _, cons a as, cons b bs => cons (a + b) (add as bs)
# end Vector
```

上述したように、引数 ``{n : Nat}`` は定義内で固定し続けることができないため、パターンマッチングの一部のならざるを得ない。Leanの以前のバージョンでは、ユーザーはこのような余分な判別子を含めなければならないことが面倒だとしばしば感じていた。そこで、Lean 4は新機能*discriminant refinement*(判別子の絞り込み)を実装した。この機能は余分な判別子を自動でパターンマッチングに含める。

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def add [Add α] {n : Nat} : Vector α n → Vector α n → Vector α n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a + b) (add as bs)
# end Vector
```

*auto bound implicits*(自動束縛暗黙引数)機能と組み合わせると、``add`` の定義をより簡潔に書くことができる:

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def add [Add α] : Vector α n → Vector α n → Vector α n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a + b) (add as bs)
# end Vector
```

これらの新機能を使うことで、前節で定義した他のベクトル関数を次のようによりコンパクトに書くことができる:

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def head : Vector α (n+1) → α
  | cons a as => a

def tail : Vector α (n+1) → Vector α n
  | cons a as => as

theorem eta : (v : Vector α (n+1)) → cons (head v) (tail v) = v
  | cons a as => rfl

def map (f : α → β → γ) : Vector α n → Vector β n → Vector γ n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (f a b) (map f as bs)

def zip : Vector α n → Vector β n → Vector (α × β) n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a, b) (zip as bs)
# end Vector
```

## Match Expressions (マッチ式)

Leanは、多くの関数型言語で見られる*match-with*式のコンパイラも提供している。

```lean
def isNotZero (m : Nat) : Bool :=
  match m with
  | 0   => false
  | n+1 => true
```

``match`` は普通のパターンマッチングによる定義とあまり変わらないように見える。しかし、``match`` のポイントは、定義内のどこでも使えることと、任意の引数に対して使えることである。

```lean
def isNotZero (m : Nat) : Bool :=
  match m with
  | 0   => false
  | n+1 => true

def filter (p : α → Bool) : List α → List α
  | []      => []
  | a :: as =>
    match p a with
    | true => a :: filter p as
    | false => filter p as

example : filter isNotZero [1, 0, 0, 3, 0] = [1, 3] := rfl
```

別の例を挙げる:

```lean
def foo (n : Nat) (b c : Bool) :=
  5 + match n - 5, b && c with
      | 0,   true  => 0
      | m+1, true  => m + 7
      | 0,   false => 5
      | m+1, false => m + 3

#eval foo 7 true false

example : foo 7 true false = 9 := rfl
```

Leanは、システムの全ての部分で、パターンマッチングを実装するために内部で ``match`` 構文を使用する。したがって、以下の4つの定義は全て同じ効果を持つ。

```lean
def bar₁ : Nat × Nat → Nat
  | (m, n) => m + n

def bar₂ (p : Nat × Nat) : Nat :=
  match p with
  | (m, n) => m + n

def bar₃ : Nat × Nat → Nat :=
  fun (m, n) => m + n

def bar₄ (p : Nat × Nat) : Nat :=
  let (m, n) := p; m + n
```

命題を分解する際には、上記の変形版が役に立つ:

```lean
variable (p q : Nat → Prop)

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y
  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
        : ∃ x y, p x ∧ q y :=
  match h₀, h₁ with
  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y :=
  fun ⟨x, px⟩ ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
        : ∃ x y, p x ∧ q y :=
  let ⟨x, px⟩ := h₀
  let ⟨y, qy⟩ := h₁
  ⟨x, y, px, qy⟩
```

## Exercises (練習問題)

1. 名前の衝突を避けるために名前空間 ``Hidden`` を開き、等式コンパイラを使って自然数上の加法、乗法、べき乗を定義せよ。次に、等式コンパイラを使って、それらの基本的な性質を証明せよ。

2. 同様に、等式コンパイラを使ってリストに対する基本的な操作(``reverse`` 関数など)を定義し、リストに関する定理を帰納法で証明せよ。例えば、任意のリストに対して、``reverse (reverse xs) = xs`` となることを示せ。

3. 累積再帰を実行する自然数上の関数を自分で定義せよ。同様に、``WellFounded.fix`` を自分で定義する方法を見つけられるか試してみよ。

4. 節[Dependent Pattern Matching (依存パターンマッチング)](#dependent-pattern-matching-依存パターンマッチング)の例に従って、2つのベクトル ``va`` ``vb`` を受け取り、``va`` の末尾に ``vb`` を追加したベクトルを返す関数を定義せよ。これは厄介で、補助関数を定義しなければならないだろう。

5. 次のような算術式の型を考える。ここで、``var n`` は変数 ``vₙ``を、``const n`` は値が ``n`` である定数を表す。

```lean
inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr

open Expr

def sampleExpr : Expr :=
  plus (times (var 0) (const 7)) (times (const 2) (var 1))
```

ここで、``sampleExpr`` は ``(v₀ * 7) + (2 * v₁)`` を表す。

各 ``var n`` を ``v n`` に評価した上で、このような式(``Expr`` の項)を評価する関数を書け。

```lean
# inductive Expr where
#   | const : Nat → Expr
#   | var : Nat → Expr
#   | plus : Expr → Expr → Expr
#   | times : Expr → Expr → Expr
#   deriving Repr
# open Expr
# def sampleExpr : Expr :=
#   plus (times (var 0) (const 7)) (times (const 2) (var 1))
def eval (v : Nat → Nat) : Expr → Nat
  | const n     => sorry
  | var n       => v n
  | plus e₁ e₂  => sorry
  | times e₁ e₂ => sorry

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

-- 次のコマンドを実行せよ。`47` が出力されたら正解である。
-- #eval eval sampleVal sampleExpr
```

補助関数 ``simpConst`` を使って、``5 + 7`` のような部分項を ``12`` に単純化する「定数融合関数」``fuse`` を実装せよ。``plus`` や ``times`` を単純化するために、まず引数を再帰的に単純化せよ。次に ``simpConst`` を適用して結果の単純化を試みよ。

```lean
# inductive Expr where
#   | const : Nat → Expr
#   | var : Nat → Expr
#   | plus : Expr → Expr → Expr
#   | times : Expr → Expr → Expr
#   deriving Repr
# open Expr
# def eval (v : Nat → Nat) : Expr → Nat
#   | const n     => sorry
#   | var n       => v n
#   | plus e₁ e₂  => sorry
#   | times e₁ e₂ => sorry
def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)  => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

def fuse : Expr → Expr := sorry

theorem simpConst_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (simpConst e) = eval v e :=
  sorry

theorem fuse_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (fuse e) = eval v e :=
  sorry
```

最後の2つの定理は、``simpConst`` や ``fuse`` が式の値を保存することを表す。
