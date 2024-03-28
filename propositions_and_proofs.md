# Propositions and Proofs (命題と証明)

第2章で、Leanにおいて項と関数を定義する方法を見てきた。この章では、依存型理論の言語を用いて数学的な主張と証明を書く方法を学ぶ。

## Propositions as Types (型としての命題)

依存型理論の言語で定義された項に関する命題を証明するための戦略の一つは、定義に用いる言語の上に命題に用いる言語と証明に用いる言語を重ねることである。しかし、複数の言語を使う必要はない。
依存型理論は、命題と証明を同じ一般的な枠組みで表現するのに十分な柔軟さと表現力を兼ね備えている。

例えば、命題を表す新しい型 ``Prop`` を導入することができる。さらに、他の命題から新しい命題を構築するコンストラクタを導入することができる。

```lean
# def Implies (p q : Prop) : Prop := p → q
#check And     -- Prop → Prop → Prop
#check Or      -- Prop → Prop → Prop
#check Not     -- Prop → Prop
#check Implies -- Prop → Prop → Prop

variable (p q r : Prop)
#check And p q                      -- Prop
#check Or (And p q) r               -- Prop
#check Implies (And p q) (And q p)  -- Prop
```

それから、各要素 ``p : Prop`` に対して、``p`` の証明の型 ``Proof p`` を導入できる。
「公理」とは、``Proof p`` のような命題の証明の型を持った定数である。

```lean
# def Implies (p q : Prop) : Prop := p → q
# structure Proof (p : Prop) : Type where
#   proof : p
#check Proof   -- Proof (p : Prop) : Type

axiom and_comm (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q : Prop)
#check and_comm p q     -- and_comm p q : Proof (Implies (p ∧ q) (q ∧ p))
#check and_comm q p     -- and_comm q p : Proof (Implies (q ∧ p) (p ∧ q))
```

公理だけでなく、既存の証明から新しい証明を作るためのルールも必要である。例えば、命題論理の証明系の多くには、"modus ponens(モーダス・ポネンス)"という推論規則がある。

> modus ponens : ``Implies p q`` の証明と ``p`` の証明があれば、そこから ``q`` の証明が得られる。

Leanではモーダス・ポネンスを次のように表現できる。

```lean
# def Implies (p q : Prop) : Prop := p → q
# structure Proof (p : Prop) : Type where
#   proof : p
axiom modus_ponens : (p q : Prop) → Proof (Implies p q) → Proof p → Proof q
```

一般的に、命題論理のための自然演繹のシステムは次の推論規則も採用している:

> 含意導入 : ``p`` を仮定すると ``q`` の証明が得られるとする。このとき、``Implies p q`` の証明が得られる。

含意導入はLean上で次のように表現できる。

```lean
# def Implies (p q : Prop) : Prop := p → q
# structure Proof (p : Prop) : Type where
#   proof : p
axiom implies_intro : (p q : Prop) → (Proof p → Proof q) → Proof (Implies p q)
```

以上の手法は、命題と証明の合理的な構築方法を提供する。この手法において、ある式 ``t`` が命題 ``p : Prop`` の正しい証明であることを確定させるには、``t`` が ``Proof p`` という型を持つことをチェックすればよい。

いくつかの簡略化が可能である。まず、命題 ``p : Prop`` があるとき、``p`` 自体を型として解釈することができる。さらに、型 ``p`` を ``p`` の証明の型と解釈する。つまり、型 ``p`` と型 ``Proof p`` を同一視する。すると、「``t`` は ``p`` の証明である」という主張をシンプルに ``t : p`` と書くことができる。
この簡略化により、毎回 ``Proof`` と書く手間が省ける。

さらにこの手法を発展させる。命題 ``p`` と ``q`` の間の含意 ``Implies p q`` は、``p`` の任意の要素に``q`` の要素を一つ割り当てる関数 ``p → q`` と同一視できる。結果として、``Implies`` という結合子の導入は不要である。含意の型 ``Implies p q`` の代わりに、依存型理論の関数の型 ``p → q`` を使えばよいのである。

これが*Calculus of Constructions*のアプローチであり、Leanはこのアプローチを採用している。自然演繹の証明系における含意の関する規則が、関数のラムダ抽象と適用に関する規則と正確に対応しているという事実は、*Curry-Howard isomorphism*(カリー=ハワード同型)の一例であり、*proposition-as-types*(型としての命題)パラダイムとして知られている。実は、型 ``Prop`` は前章で説明した型階層の最下層である型 ``Sort 0`` の糖衣構文である(``Prop`` と ``Sort 0`` は全く同じ意味である)。さらに言えば、型 ``Type u`` は型 ``Sort (u+1)`` の糖衣構文に過ぎない。``Prop`` はいくつか特別な特徴を持っているが、他の型宇宙と同様に、アローコンストラクタの下で閉じている。つまり、``p q : Prop`` ならば ``p → q : Prop`` である(``α β : Type`` ならば ``α → β : Type`` であるのと同様である)。

「型としての命題」について考えるには、少なくとも2通りの方法がある。論理学や数学について構成主義的な立場をとる人にとっては、「型としての命題」は「命題とはどういうものか」を忠実に表現している。命題 ``p`` は ``p`` の証明を構成するデータの型を表している。``p`` の証明とは、単に正しく型付けされた項 ``t : p`` である。

このような主義に傾倒していない人にとって、「型としての命題」はむしろ単純なコーディング・トリックだと考えることができる。各命題 ``p`` に対して、 ``p`` が偽なら ``p`` に空の型を関連付ける。``p`` が真なら ``p`` にただ一つの項 ``*`` を持つ型を関連付ける。後者のとき、``p`` (に関連付けられた型)を *inhabited*(有項) と呼び、型 ``p`` が持つ項 ``*`` を*inhabitant*(住人) と呼ぶ。このとき、たまたま、関数の適用と抽象化の規則が、``Prop`` のどの要素が有項かを追跡するのに便利だったのである。つまり、項 ``t : p`` を構築することが、``p`` が真であることを保証してくれるのである。
このとき、``p`` の住人 ``t`` とは「``p`` が真であるという事実」のことだと考えることができる。そうすると、``p → q`` の証明とは「``p`` が真であるという事実」を受け取って「``q`` が真であるという事実」を返す関数のことだと考えることができる。

実際、Leanのカーネルは ``(fun x => t) s`` と ``t[s/x]``(項 ``t`` の中の全ての ``x`` を ``s`` で置き換えた項) をdefinitionally equalとみなすのと同様に、任意の ``p : Prop`` に対して任意の2つの項 ``t1 t2 : p`` をdefinitionally equalとみなす。``t1 t2 : p`` をdefinitionally equalとみなすことは*proof irrelevance*(証明無関係)と呼ばれ、前段落の解釈と矛盾しない。つまり、証明 ``t : p`` は依存型理論の言語の中で普通の項として扱うことができるが、``t`` は ``p`` が真であるという事実以上の情報は持っていないということである。

以上で提案した「型としての命題」パラダイムについて考えるための2つの方法は、根本的なところで異なっている。構成主義的な観点からすると、証明は抽象的な数学的対象であり、依存型理論において適切な項で「表現」される。対照的に、前述のコーディング・トリックの観点からすると、項 ``t : p`` そのものは何も面白いものを示さない。むしろ、項を書き下し、その項がきちんと型付けされていることを確認することで、問題の命題が真であることを保証するのである。つまり、項「そのもの」が証明なのである。

以下の説明では、ある項がある命題の証明を「構築する」「生成する」「返す」と表現したり、単にある項がある命題の証明「である」と表現したり、この両方の表現を使うことにする。これは、計算機科学者が、あるプログラムがある関数を「計算する」と言いながら、時にはそのプログラムがその関数「である」と言うことで、構文論と意味論の区別を曖昧にすることがあるのと似たようなものである。

いずれにせよ、本当に重要なのは次のことである: 依存型理論の言語で数学的な命題 ``p`` を形式的に表現するには、項 ``p : Prop`` を構築する必要がある。命題 ``p`` を「証明」するには、項 ``t : p`` を構築する必要がある。証明支援系Leanの仕事は、このような項 ``t`` を構築する手助けをし、そして ``t`` が適切な形をとっていて正しい型を持つことを検証することである。

## Working with Propositions as Types (「型としての命題」を実践する)

「型としての命題」パラダイムにおいては、``→`` と命題だけを含む定理はラムダ抽象と関数適用を使って証明することができる。Leanでは、``theorem`` コマンドを使うと新しい定理を導入できる。

```lean
variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
```

この証明を、型 ``α → β → α`` (``α`` と ``β`` は型 ``Type`` の項) の項 ``fun x : α => fun y : β => x`` と比較してほしい。``fun x : α => fun y : β => x`` は引数 ``x : α`` と引数 ``y : β`` をとり、``x`` を返す。
``p → q → p`` の証明は同じ形をとる。唯一の違いは ``p`` と ``q`` が ``Type`` ではなく ``Prop`` の項であることだけである。
直観的には、我々の ``p → q → p`` の証明は命題 ``p : Prop`` と命題 ``q : Prop`` が正しいことを前提とし、最初の前提から ``p`` が正しいことを(自明に)結論づける。

``theorem`` コマンドは ``def`` コマンドと全く同じである。つまり、命題と型の対応の下で、定理 ``p → q → p`` を証明することは、型 ``p → q → p`` の要素を定義することと全く同じである。実際、Leanのカーネルの型チェッカーにとって、``theorem`` コマンドと ``def`` コマンドの間に違いはない。

しかしながら、定義と定理の間にはいくつかの実用的な違いがある。通常、定理の「定義」を展開する必要はない。証明無関係の原則により、ある定理の任意の2つの証明はdefinitionally equalである。一度定理の証明が完成したら、通常はその定理の証明が存在することだけが分かればよく、その証明が何であるかは重要ではない。この事実をふまえ、Leanは証明に*irreducible*とタグ付けする。ファイルを処理するとき、このタグはパーサー(より正確には*elaborator*)に対して、「このタグが付いたものを展開する必要はない」というヒントとして機能する。実際、Leanは一般的に証明の処理とチェックを平行して行うことができる。これは、ある証明の正しさを検証する際に、他の証明の詳細を知る必要がないからできることである。

定義と同様に、``#print`` コマンドは定理の証明を表示する。

```lean
variable {p : Prop}
variable {q : Prop}
theorem t1 : p → q → p := fun hp : p => fun hq : q => hp

#print t1    -- ∀ {p q : Prop}, p → q → p := fun {p q} hp hq => hp
```

ラムダ抽象 ``hp : p`` と ``hq : q`` は ``p → q → p`` の証明における一時的な前提と見なせることに注意してほしい。また、Leanでは、最後の項 ``hp`` の型を、``show`` 文で明示的に指定することができる。

```lean
# variable {p : Prop}
# variable {q : Prop}
theorem t1 : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp      -- show <型> from <項>
```

このような情報を追加することで、証明の分かりやすさを向上させ、証明を書く際の誤りを発見しやすくすることができる。``show`` コマンドは型に注釈をつける以上のことはしない。内部的には、これまで見てきた ``t1`` の表現は全て同じ項を生成している。

通常の定義と同様に、``theorem`` コマンドにおいても、ラムダ抽象された変数をコロンの左側に持ってくることができる。

```lean
# variable {p : Prop}
# variable {q : Prop}
theorem t1 (hp : p) (hq : q) : p := hp

#print t1    -- p → q → p
```

定理 ``t1`` は関数適用と同様に他の項に適用することができる。

```lean
# variable {p : Prop}
# variable {q : Prop}
theorem t1 (hp : p) (hq : q) : p := hp

axiom hp : p

theorem t2 : q → p := t1 hp
```

ここで、``axiom`` 宣言は与えられた型の項の存在を無条件に認めるため、``axiom`` コマンドの使い方によっては論理的整合性を損なう可能性がある。例えば、``axiom`` コマンドにより空の型 ``False`` が項を持つことを認めることさえ可能である。

```lean
axiom unsound : False
-- `False`(偽)からは任意の命題を示すことができる
theorem ex : 1 = 0 :=    -- 本来は偽の命題
  False.elim unsound
```

「公理」``hp : p`` を宣言することは、``hp`` の存在を無条件に認め、``hp`` により ``p`` が真であると宣言することと等価である。``p`` が真だと主張する公理 ``hp : p`` に定理 ``t1 : p → q → p`` を適用すると、定理 ``t1 hp : q → p`` が得られる。

定理 ``t1`` は次のように書けることを思い出そう。

```lean
theorem t1 {p q : Prop} (hp : p) (hq : q) : p := hp

#print t1    -- ∀ {p q : Prop}, p → q → p := fun {p q} hp hq => hp
```

``t1`` の型は ``∀ {p q : Prop}, p → q → p`` だと表示される。これは、「任意の命題のペア ``p q`` について、``p → q → p`` が成立する」と読める。
この結果を用いると、``t1`` の全ての引数をコロンの右側に持っていくことができる。

```lean
theorem t1 : ∀ {p q : Prop}, p → q → p :=
  fun {p q : Prop} (hp : p) (hq : q) => hp
```

``p`` と ``q`` が ``variable`` コマンドを使って宣言されているなら、Leanは自動的に ``p`` と ``q`` を全称化する。

```lean
variable {p q : Prop}

theorem t1 : p → q → p := fun (hp : p) (hq : q) => hp

#print t1    -- ∀ {p q : Prop}, p → q → p := fun {p q} hp hq => hp
```

「型としての命題」対応に従って、``p`` は正しいという前提 ``hp`` を別の変数として宣言することができる。

```lean
variable {p q : Prop}
variable (hp : p)

theorem t1 : q → p := fun (hq : q) => hp

#print t1    -- ∀ {p q : Prop}, p → q → p := fun {p q} hp hq => hp
```

Leanはこの証明が ``hp`` を使っていることを検出し、自動的に ``hp : p`` を前提に追加する。どの例でも ``#print t1`` は ``∀ p q : Prop, p → q → p`` を表示する。この型は ``∀ (p q : Prop) (hp : p) (hq : q), p`` とも書けることに注意してほしい。

``t1`` を全称化すれば、``t1`` を様々な命題のペアに適用させることで、一般的な定理 ``t1`` の様々な例を得ることができる。

```lean
theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp

variable (p q r s : Prop)

#check t1 p q                -- p → q → p
#check t1 r s                -- r → s → r
#check t1 (r → s) (s → r)    -- (r → s) → (s → r) → r → s

variable (h : r → s)
#check t1 (r → s) (s → r) h  -- (s → r) → r → s
```

再び、「型としての命題」対応を利用すると、``r → s`` 型の変数 ``h`` を「``r → s`` は真である」という前提とみなすことができる。

別の例として、前章で説明した合成関数を、今度は型の代わりに命題を使って考えてみよう。

```lean
variable (p q r s : Prop)

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)
```

命題論理の定理として見ると、``t2`` は何を表現しているだろうか？

この例で使ったように、前提として使える証明項の名前にはUnicode数字添字を使うのが便利である。これらは``\0``、``\1``、``\2``、...と打つと入力できる。

## Propositional Logic (命題論理)

Leanでは標準的な論理的結合子と記法の全てが定義されている。命題論理の結合子は次のように表す:

| Ascii             | Unicode   | エディターでの入力方法         | 定義         |
|-------------------|-----------|------------------------------|--------------|
| True              |           |                              | True         |
| False             |           |                              | False        |
| Not               | ¬         | ``\not``, ``\neg``           | Not          |
| /\\               | ∧         | ``\and``                     | And          |
| \\/               | ∨         | ``\or``                      | Or           |
| ->                | →         | ``\to``, ``\r``, ``\imp``    |              |
| <->               | ↔         | ``\iff``, ``\lr``            | Iff          |

これらは ``Prop`` 型の項(命題)を取り、``Prop`` 型の新しい項(命題)を返す。

```lean
variable (p q : Prop)

#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p
```

演算の順序は次の通り: 単項否定 ``¬`` が一番最初に結合し、次に ``∧``、``∨``、``→``、最後に ``↔`` が結合する。例えば、``a ∧ b → c ∨ d ∧ e`` と書かれていたら、それは ``(a ∧ b) → (c ∨ (d ∧ e))`` のことである。
引数の型が ``Prop`` であっても他の型であっても、``→`` は右から順に結合していくことを忘れないでほしい。つまり、``p q r : Prop`` とすると、``p → q → r`` という式は ``p → (q → r)`` と同じである。これは、「カリー化」された ``p ∧ q → r`` である。

前節ではラムダ抽象を ``→`` の「導入則」とみなすことができることを説明した。ラムダ抽象が含意命題を「導入」あるいは構築する方法だとすると、関数適用は「含意の除去則」だとみなせる。つまり、関数適用は証明の中で含意を「除去する」あるいは使う方法である。他の命題論理の結合子はLeanのライブラリのファイル ``Init/Prelude.lean`` (ライブラリの階層構造については[Importing Files (ファイルのインポート)](./interacting_with_lean.md#importing-files-ファイルのインポート)を参照のこと)で定義されている。それぞれの結合子には正規化された導入則と除去則が存在する。

### Conjunction (連言)

式 ``And.intro h1 h2`` は証明 ``h1 : p`` と証明 ``h2 : q`` を使って ``p ∧ q`` の証明を構築する。``And.intro`` は一般的に「連言の導入則」と表現される。次の例では、``And.intro`` を使って ``p → q → p ∧ q`` の証明を作る。

```lean
variable (p q : Prop)

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

#check fun (hp : p) (hq : q) => And.intro hp hq
```

``example`` コマンドは、定理に名前を付けたり、永続する文脈に定理を保存することなく、定理を記述するのに使う。基本的には、``example`` コマンドは与えられた項が与えられた型を持っているかどうかをチェックするだけである。実例を示すのに便利で、よく使うコマンドである。

式 ``And.left h`` は証明 ``h : p ∧ q`` から ``p`` の証明を作る。同様に、``And.right h`` は証明 ``h : p ∧ q`` から ``q`` の証明を作る。これらは一般的に「左連言除去則」と「右連言除去則」として知られている。

```lean
variable (p q : Prop)

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h
```

ここまでの知識を使って、次のように ``p ∧ q → q ∧ p`` を証明することができる。

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)
```

連言導入と連言除去は直積ペアの構築と射影の操作に似ていることに注意してほしい。``p : Prop``、``q : Prop``、``hp : p``、``hq : q`` のとき、``And.intro hp hq`` は型 ``p ∧ q : Prop`` を持つ。一方、``p : Type``、``q : Type``、``hp : p``、``hq : q`` のとき、``Prod hp hq`` は型 ``p × q : Type`` を持つ。
この類似性は「カリー=ハワード同型対応」の別の例である。この類似性によると、今作った証明は直積ペアの要素を入れ替える関数に似ていることになる。しかし、含意と関数型コンストラクタとは対照的に、Leanでは ``∧`` と ``×`` は別々に扱われている。

[9章 Structures and Records (構造体とレコード)](./structures_and_records.md)で、Leanには*structures*(構造体)と呼ばれる型があることを学ぶ。構造体 ``S`` は適切な引数の列から ``S`` の要素を構築する単一で正規の*constructor*(コンストラクタ)によって定義される。任意の ``p q : Prop`` に対して、``p ∧ q`` は構造体の一例である。構造体 ``p ∧ q`` の要素を構築する正規の方法は、適切な引数 ``hp : p`` と ``hq : q`` に ``And.intro`` を適用することである。
Leanでは、関連する型が帰納型であり、文脈から型推論できる場合、*anonymous constructor*(匿名コンストラクタ)表記 ``⟨arg1, arg2, ...⟩`` を使うことができる。特に、``And.intro hp hq`` の代わりに ``⟨hp, hq⟩`` と書くことがよくある。

```lean
variable (p q : Prop)
variable (hp : p) (hq : q)

#check (⟨hp, hq⟩ : p ∧ q)
```

角括弧 ``⟨ ⟩`` は ``\<`` ``\>`` と打つことで入力できる。

他にもLeanには便利な構文機能がある。項 ``e`` が(パラメータをとる可能性のある)帰納型 ``Foo`` を持つとき、``e.bar`` は ``Foo.bar e`` の略記である。この記法は名前空間を開くことなく関数にアクセスする便利な方法を提供する。例えば、次の2つの項は全く同じである:

```lean
variable (xs : List Nat)

#check List.length xs
#check xs.length
```

結果として、``h : p ∧ q`` があるとき、``And.left h`` の代わりに ``h.left`` と書け、``And.right h`` の代わりに ``h.right`` と書ける。従って、上記の例は次のように簡潔に書ける:

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  ⟨h.right, h.left⟩
```

簡潔さと難解さは紙一重であり、このように情報を省略することは時として証明を読みにくくする。しかし、上のような簡単な例で、``h`` の型と構築したい型がはっきりしている場合、この記法は簡潔で効果的である。

``And.`` のような構築を繰り返すことは普通である。Leanはネストされた角括弧を外すことができる。このとき、各引数は右から結合する。したがって、次の2つの証明は等価である:

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, ⟨h.left, h.right⟩⟩

example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, h.left, h.right⟩
```

これも便利である。

### Disjunction (選言)

式 ``Or.intro_left q hp`` は 証明 ``hp : p`` から ``p ∨ q`` の証明を作る。同様に、``Or.intro_right p hq`` は証明 ``hq : q`` から ``p ∨ q`` の証明を作る。これらは「左選言導入則」と「右選言導入則」に相当する。

```lean
variable (p q : Prop)
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq
```

「選言除去則」は少し複雑である。``p`` から ``r`` が導かれることと、 ``q`` から ``r`` が導かれることの両方を示せば、``p ∨ q`` から ``r`` を証明できるという考えを使う。つまり、これは場合分けによる証明である。式 ``Or.elim hpq hpr hqr`` の中で、``Or.elim`` は3つの引数 ``hpq : p ∨ q``、``hpr : p → r``、
``hqr : q → r`` を取り、``r`` の証明を作る。次の例の中で、``p ∨ q → q ∨ p`` を証明するのに ``Or.elim`` を使う。

```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)
```

ほとんどの場合、``Or.intro_right`` の第1引数と ``Or.intro_left`` の第1引数はLeanによって自動的に推論される。Leanは ``Or.intro_right _`` の略記として ``Or.inr`` を、``Or.intro_left _`` の略記として ``Or.inl`` を提供する。したがって、上記の証明はより簡潔に書ける:

```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)
```

この簡潔な式の中に、Leanが ``hp`` と ``hq`` の型を推論するのに十分な情報が含まれていることに注意してほしい。しかし、型注釈を用いた長い記述を用いることは、証明を読みやすくし、エラーを発見してデバッグするのに役立つ。

``Or`` は2つのコンストラクタを持つ、つまり単一で正規のコンストラクタを持たないため、``Or`` の構築のために匿名コンストラクタを使うことはできない。しかし、``Or.elim h`` の代わりに ``h.elim`` と書くことはできる:

```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)
```

繰り返しになるが、このような略記が読みやすさを向上させるか低下させるか、書き手が判断する必要がある。

### Negation and Falsity (否定と恒偽)

否定 ``¬p`` は ``p → False`` と定義される。したがって、``¬p`` の証明は ``p`` から矛盾を導くことで得られる。同様に、式 ``hnp hp`` は ``hp : p`` と ``hnp : ¬p`` から ``False`` の証明を作る。
次の例ではこれらの規則の両方を使って ``(p → q) → ¬q → ¬p`` の証明を作る(記号 ``¬`` は ``\not`` あるいは ``\neg`` と打つことで入力できる)。

```lean
variable (p q : Prop)

example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)
```

結合子 ``False`` は単一の除去則 ``False.elim`` を持つ。``False.elim`` は矛盾からは任意の命題が導かれるという事実を表現している。この規則は*ex falso* (*ex falso sequitur quodlibet*の略記)あるいは*principle of explosion*(爆発律)と呼ばれる。

```lean
variable (p q : Prop)

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
```

恒偽から導かれる任意の命題 ``q`` は暗黙の引数であり、自動的に型推論される。矛盾する前提から任意の命題を導くパターンは非常によく見られ、``absurd`` で表現される。

```lean
variable (p q : Prop)

example (hp : p) (hnp : ¬p) : q := absurd hp hnp
```

次は ``¬p → q → (q → p) → r`` の証明である:

```lean
variable (p q r : Prop)

example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp
```

ちなみに、``False`` が除去則しか持たないように、``True`` は導入則である ``True.intro : True`` しか持たない。つまり、``True`` は単に真であり、``True.intro`` という正規の証明を持っている。

### Logical Equivalence (論理的同値)

式 ``Iff.intro h1 h2`` は ``h1 : p → q`` と ``h2 : q → p`` から ``p ↔ q`` の証明を作る。 式 ``Iff.mp h`` は ``h : p ↔ q`` から ``p → q`` の証明を作る。同様に、``Iff.mpr h`` は ``h : p ↔ q`` から ``q → p`` の証明を作る。以下は ``p ∧ q ↔ q ∧ p`` の証明である。

```lean
variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))

#check and_swap p q    -- p ∧ q ↔ q ∧ p

variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h
```

匿名コンストラクタ記法を使って、``p → q`` の証明と　``q → p`` の証明から ``p ↔ q`` の証明を構築することができる。また、``mp`` と ``mpr`` について ``.`` に関する記法が使える。これらを使うと、上記の例は次のように簡潔に書くことができる:

```lean
variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩

example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h
```

## Introducing Auxiliary Subgoals (補助的なサブゴールの導入)

そろそろ長い証明を書く際に役に立つ機能 ``have`` の紹介をする頃合いだろう。``have`` は証明の中で補助的なサブゴールを導入する。次は前節から抜粋した短い例である。

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp
```

内部的には、式 ``have h : p := s; t`` は項 ``(fun (h : p) => t) s`` を作る。つまり、``s`` は ``p`` の証明であり、``t`` は 前提 ``h : p`` の下で欲しい結論の証明であり、``s`` と ``t`` はラムダ抽象と関数適用によって組み合わせられる。``have`` は、長い証明を構築する際に、最終的なゴールに至るための踏み台として使えるため、非常に便利である。

Leanは、ゴールから*backward reasoning*(後ろ向き推論)する構造化された方法もサポートしている。これは通常の数学における「Aを示すにはBを示せば十分である」という証明を模した手法である。次の例は、前の証明の最後の2行を単に並べ替えたものである。

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h
```

``suffices hq : q`` を使った後は2つのゴールを示す必要がある。まず、``q ∧ p`` を示すには ``q`` を示せば十分であることを実際に示す必要がある。そのためには追加された前提 ``hq : q`` を使って元のゴール ``q ∧ p`` を証明すればよい。 最後に、``q`` を示す必要がある。

## Classical Logic (古典論理)

これまで見てきた導入則と除去則は全て構成的論理(直観主義論理)のものである。これは「型としての命題」対応に基づいた論理的結合子の計算論的理解を反映したものである。通常の古典論理では、以上の導入則と除去則に加え、排中律 ``p ∨ ¬p`` を認める。この原則を使うには、名前空間 ``Classical`` を開く必要がある。

```lean
open Classical

variable (p : Prop)
#check em p      -- p ∨ ¬p
```

直感的には、構成的論理の「Or」は非常に強い主張であり、``p ∨ q`` を主張することは、どちらが正しいかを知っていることに等しい。リーマン予想を ``RH`` と表すと、古典論理を採用している数学者は、``RH`` と ``¬RH`` のどちらが正しいのか分からないうちに ``RH ∨ ¬RH`` を主張することを厭わない。構成的論理を採用すると、このような主張の仕方はできない。

排中律の帰結として、二重否定除去則が得られる。

```lean
open Classical

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)
```

``¬p`` を仮定すると ``False`` が導かれるとき、二重否定除去を使うと命題 ``p`` を証明することができる。なぜなら、仮定 ``¬p`` から ``False`` を導いたことは、``¬¬p`` を証明したことと同義だからである。つまり、二重否定消去を使えば、構成的論理では一般には不可能な、矛盾による証明を行うことができる。練習として、逆を、つまり ``dne`` から ``em`` が証明できることを示してみよう。

古典論理の公理はまた、``em`` により正当化される追加の証明パターンを使えるようにする。例えば、場合分けによる証明を行うことができる:

```lean
open Classical
variable (p : Prop)

example (h : ¬¬p) : p :=
  byCases
    (fun h1 : p => h1)
    (fun h1 : ¬p => absurd h1 h)
```

``hpq : p → q``、``hnpq : ¬p → q`` のとき、``byCases hpq hnpq`` は ``q`` の証明を作る。

あるいは、矛盾により証明を行うこともできる:

```lean
open Classical
variable (p : Prop)

example (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p =>
     show False from h h1)
```

``hnpf : ¬p → False`` のとき、``byContradiction hnpf`` は ``p`` の証明を作る。

もし構成的論理の考え方に慣れていないなら、古典論理的な推論がどこで使われているのか感覚を掴むのに時間がかかるかもしれない。次の例は、構成的論理では、 ``p`` と ``q`` が両立しないと分かってもどちらが偽であるかは必ずしも分からないので、古典論理が必要である:

```lean
# open Classical
# variable (p q : Prop)
example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p =>
      Or.inr
        (show ¬q from
          fun hq : q =>
          h ⟨hp, hq⟩))
    (fun hp : ¬p =>
      Or.inl hp)
```

構成的論理には、排中律や二重否定除去のような原則が許される状況が「ある」ことを後に学ぶ。そのような状況では、Leanは排中律に頼ることなく古典論理的な推論の使用をサポートする。

古典論理的な推論を行うためにLeanで採用されている全ての公理の一覧は[12章 Axioms and Computation (公理と計算)](./axioms_and_computation.md)で論じられている。

## Examples of Propositional Validities (命題論理における恒真式の例)

Leanの標準ライブラリは命題論理における恒真式の証明をいくつも含んでいる。その全ては読者自身の証明を書く際に自由に用いてよい。命題論理における恒真式のいくつかを以下に示す。

可換性:

1. ``p ∧ q ↔ q ∧ p``
2. ``p ∨ q ↔ q ∨ p``

結合性:

3. ``(p ∧ q) ∧ r ↔ p ∧ (q ∧ r)``
4. ``(p ∨ q) ∨ r ↔ p ∨ (q ∨ r)``

分配性:

5. ``p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)``
6. ``p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)``

他の性質:

7. ``(p → (q → r)) ↔ (p ∧ q → r)``
8. ``((p ∨ q) → r) ↔ (p → r) ∧ (q → r)``
9. ``¬(p ∨ q) ↔ ¬p ∧ ¬q``
10. ``¬p ∨ ¬q → ¬(p ∧ q)``
11. ``¬(p ∧ ¬p)``
12. ``p ∧ ¬q → ¬(p → q)``
13. ``¬p → (p → q)``
14. ``(¬p ∨ q) → (p → q)``
15. ``p ∨ False ↔ p``
16. ``p ∧ False ↔ False``
17. ``¬(p ↔ ¬p)``
18. ``(p → q) → (¬q → ¬p)``

これらは古典論理的な推論を必要とする:

19. ``(p → r ∨ s) → ((p → r) ∨ (p → s))``
20. ``¬(p ∧ q) → ¬p ∨ ¬q``
21. ``¬(p → q) → p ∧ ¬q``
22. ``(p → q) → (¬p ∨ q)``
23. ``(¬q → ¬p) → (p → q)``
24. ``p ∨ ¬p``
25. ``(((p → q) → p) → p)``

``sorry`` は魔法のようにあらゆる証明を生成したり任意の型の項を提供したりする。もちろん、``sorry`` は証明方法としては不健全である。例えば、``sorry`` を使って ``False`` を証明することができる。Leanは、``sorry`` に依存する定理を使ったり、インポートしたりすると、深刻な警告を発する。しかし、長い証明を段階的に構築する際は便利である。サブ証明を ``sorry`` で埋めながら、証明をトップダウンで書いてみよう。``sorry`` だけで構築された項をLeanが受容することを確認してほしい。そうでない場合は、修正する必要があるエラーが存在する。確認と修正が済んだら、実際の証明で ``sorry`` を一つ残らず書き換えよう。

もう一つ、便利な技がある。``sorry`` を使う代わりに、アンダースコア ``_`` をプレースホルダーとして使うことができる。アンダースコアは引数が暗黙であることをLeanに伝えることを思い出してほしい。そしてアンダースコアはLeanによって自動的に埋められる。もしLeanがアンダースコアを埋めることに失敗したら、エラーメッセージ "don't know how to synthesize placeholder" が返され、続いて項の予想される型とその文脈で使用可能な全ての項と前提が返される。言い換えると、解決できなかったプレースホルダー1つ1つに対して、Leanはその時点で埋める必要のあるサブゴールを報告する。最終的に、プレースホルダーを段階的に埋めていくことで、証明を構築することができる。

参考として、上記のリストから抜粋した恒真式の証明の例を2つ紹介する。

```lean
open Classical

-- 分配性
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

-- 古典論理を必要とする例
example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp : p =>
  show q from
    Or.elim (em q)
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd (And.intro hp hnq) h)
```

## Exercises (練習問題)

"sorry" プレースホルダーを実際の証明で置き換えて、以下の恒真式を証明せよ。

```lean
variable (p q r : Prop)

-- ∧ と ∨ の可換性
example : p ∧ q ↔ q ∧ p := sorry
example : p ∨ q ↔ q ∨ p := sorry

-- ∧ と ∨ の結合性
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- 分配性
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- 他の性質
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
```

"sorry" プレースホルダーを実際の証明で置き換えて、以下の恒真式を証明せよ。これらは古典論理を必要とする。

```lean
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry
```

最後に、古典論理を使わずに ``¬(p ↔ ¬p)`` を証明せよ。
