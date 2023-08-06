# Quantifiers and Equality (量化子と等号)

第3章では、命題論理の結合子を含む定理の証明を構築する方法を紹介した。この章では、命題論理の結合子に加え、全称量化子、存在量化子、等号関係を用いた定理とその証明を構築する方法を紹介する。

## The Universal Quantifier (全称量化子)

任意の型 ``α`` に対して、``α`` 上の一変数述語 ``p`` は、型 ``α → Prop`` の項として表現できることに注目してほしい。この場合、``x : α`` が与えられると、``p x`` は ``x`` について ``p`` が成り立つという主張を表す。同様に、項 ``r : α → α → Prop`` は ``α`` 上の二項関係を表す。``x y : α`` が与えられると、``r x y`` は ``x`` と ``y`` の間に二項関係 ``r`` が成立するという主張を表す。

全称量化子 ``∀`` を用いた主張 ``∀ x : α, p x`` は、「全ての ``x : α`` に対して、``p x`` が成立する」という主張を表す。命題結合子と同様に、自然演繹の体系においては、全称量化子は導入則と除去則によって統制される。非形式的には、全称量化子の導入則は次のように表される:

> ``x : α`` が任意に選べる文脈で ``p x`` の証明が与えられたとき、``∀ x : α, p x`` の証明を得ることができる。

全称量化子の除去則は次のように表される:

> ``∀ x : α, p x`` の証明があるとき、任意の項 ``t : α`` に対して、``p t`` の証明を得ることができる。

含意の場合と同様に、「型としての命題」の考え方が有効である。依存関数型の導入則と除去則を思い出してほしい:

> ``x : α`` が任意に選べる文脈で型 ``β x`` の項 ``t`` が作れるとき、項 ``(fun x : α => t) : (x : α) → β x`` が作れる。

依存関数型の除去則は次のように表される:

> 項 ``s : (x : α) → β x`` が与えられたとき、型 ``α`` の任意の項 ``t : α`` に対して、項 ``s t : β t`` を得ることができる。

``p x`` が ``Prop`` 型を持つとき、型 ``(x : α) → β x`` を型 ``∀ x : α, p x`` とみなすことで、依存関数型の導入則と除去則を全称量化子の導入則と除去則とみなすことができる。これらの規則に従って、全称量化子を含む証明を構築することができる。

「型としての命題」の考え方に従って、Calculus of Constructionsでは、従属関数型と全称量化子を同一視する。つまり、任意の項 ``p`` に対して、``∀ x : α, p`` は ``(x : α) → p`` の代替表現に過ぎず、``p`` が命題のときは、後者の表現の方が自然である、と考えるのである。

通常の関数の場合、``α → β`` は ``β`` が ``x : α`` に依存しない場合の ``(x : α) → β`` だと解釈できることを思い出してほしい。同様に、命題間の含意 ``p → q`` は命題 ``q`` が ``x : p`` に依存しない場合の ``∀ x : p, q`` だと解釈することができる。

以下は、全称量化子に関する「型としての命題」対応がどのように実践されるかの例である。

```lean
example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left
```

表記上の慣習として、Leanは全称量化子に可能な限り広いスコープを与えるので、上の例では ``x`` に対する量化子のスコープを限定するために括弧が必要である。そして、``∀ y : α, p y`` を証明する正規の方法は、``y`` を任意に取り、``p y`` を証明することである。これが全称量化子の導入則の使用例である。次に、型 ``∀ x : α, p x ∧ q x`` を持つ項 ``h`` が与えられると、項 ``h y`` は型 ``p y ∧ q y`` を持つ。これが全称量化子の除去則の使用例である。連言命題 ``h y`` の左の命題を取ると、所望の結論 ``p y`` が得られる。

束縛変数の名前を変えることで同じにできる2つの式は、等価であるとみなされる(α-同値)ことを思い出してほしい。例えば、上記の例について、結論の前件と後件の両方で同じ変数名 ``x`` を用いて、証明の中では別の変数名 ``z`` を使ってインスタンスを表現することもできる。

```lean
example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α =>
  show p z from And.left (h z)
```

もう一つの例として、関係 ``r`` が推移的であることはどのように表現されるかを提示しよう:

```lean
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r                -- ∀ (x y z : α), r x y → r y z → r x z
/- (r : α → α → Prop) と 「r x y → r y z → r x z」により x,y,z の型が推論されている -/
#check trans_r a b c          -- r a b → r b c → r a c
#check trans_r a b c hab      -- r b c → r a c
#check trans_r a b c hab hbc  -- r a c
```

この例で何が起こっているのかを考えてみよう。``trans_r`` を値 ``a b c`` でインスタンス化すると、これは ``r a b → r b c → r a c`` の証明になる。これを「前提」``hab : r a b`` に適用すると、含意命題 ``r b c → r a c`` の証明が得られる。最後に、これを前提 ``hbc`` に適用すると、結論 ``r a c`` の証明が得られる。

``hab`` と ``hbc`` があれば最初の3つの引数が ``a b c`` であることは容易に推論できる。このような状況において、引数 ``a b c`` を毎回与えるのは面倒かもしれない。そのため、これらを暗黙の引数にするのが一般的である:

```lean
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r          -- r ?m.1 ?m.2 → r ?m.2 ?m.3 → r ?m.1 ?m.3
#check trans_r hab      -- r b ?m.42 → r a ?m.42
#check trans_r hab hbc  -- r a c
```

``x y z`` を暗黙の引数にする利点は、``r a c`` の証明を ``trans_r hab hbc`` と簡単に書けることである。欠点は、項 ``trans_r`` と項 ``trans_r hab`` の型を推論するのに必要な情報をLeanに与えることができないことである。最初の ``#check`` コマンドの出力は ``r ?m.1 ?m.2 → r ?m.2 ?m.3 → r ?m.1 ?m.3`` であり、暗黙の引数が特定できなかったことを示している。

次は ``r`` が同値関係であるという前提を使って初歩的な推論を行う例である:

```lean
variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd
```

全称量化子の使い方に慣れるために、この章の最後にある練習問題をいくつかやってみるとよい。

依存関数型には型付け規則があるが、全称量化子には特殊な型付け規則がある。これが ``Prop`` と他の型の違いである。``α : Sort i`` と ``β : Sort j`` があり、項 ``β`` は ``x : α`` に依存するかもしれないとする。このとき、``(x : α) → β`` は型 ``Sort (imax i j)`` の項である。ここで、``imax i j`` は ``j`` が0でないなら ``i`` と ``j`` の最大値で、``j`` が0なら0である。

``imax i j`` の定義は次のように解釈すればよい。もし ``j`` が ``0`` でないなら、``(x : α) → β`` は型 ``Sort (max i j)`` の項である。言い換えれば、``α`` から ``β`` への依存関数型は、インデックスが ``i`` と ``j`` の最大値である宇宙に「住んで」いる。他方で、``β`` が ``Sort 0``、つまり ``Prop`` の項であるとしよう。この場合、``α`` がどの階層的型宇宙に住んでいるかに関わらず、``(x : α) → β`` も ``Sort 0`` (``Prop``) の項となる。言い換えれば、``β`` が ``α`` に依存する命題であれば、 ``∀ x : α, β`` も命題であるということである。これは、``Prop`` は単なるデータの型ではなく命題の型であるという解釈を反映している。そして以上のことは ``Prop`` を*impredicative*(非可述的)にしている。

*predicative*(可述的)という用語は、20世紀初頭の数学基礎論の発展に由来する。当時、ポアンカレやラッセルといった論理学者が、集合論におけるパラドックスを、性質Aを持つ集合を量化することで性質Aを定義するときに生じる「悪循環」のせいにしたのである。任意の型 ``α`` に対して、``α`` 上の全ての(一変数)述語からなる型 ``α → Prop`` (``α`` の「べき型」)を作れることに注目してほしい。``Prop`` のimpredicativity(非可述性)とは、``α → Prop`` を量化した命題を作れることを意味する。特に、``α`` 上の述語を全称量化することで、``α`` 上の述語を定義することができ(``∀ X : α → Prop, β`` と書くことで「全ての ``α`` 上の述語に対して ``β`` が成立する」という ``α`` 上の述語を定義することができ)、これはまさにかつて問題視された類の循環である。

## Equality (等号)

ここで、Leanのライブラリで定義されている最も基本的な関係の一つである「等号関係」に注目しよう。[7章 Inductive Types (帰納型)](./inductive_types.md)では、Leanの*logical framework*(論理フレームワーク)の根本から「どのように」等号が定義されるかを説明する。その前に、ここでは等号の使い方を説明する。

もちろん、等号の基本的な性質の一つは、「等号は同値関係である」という性質である:

```lean
#check Eq.refl    -- {α : Sort u_1} (a : α) : a = a
#check Eq.symm    -- {α : Sort u} {a b : α} (h : a = b) : b = a
#check Eq.trans   -- {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c
```

Leanに暗黙の引数(ここではメタ変数として表示されている)を挿入しないように指示することで、出力を読みやすくすることができる。

```lean
universe u

#check @Eq.refl.{u}   -- ∀ {α : Sort u} (a : α), a = a
#check @Eq.symm.{u}   -- ∀ {α : Sort u} {a b : α}, a = b → b = a
#check @Eq.trans.{u}  -- ∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
```

``.{u}`` という記法は、宇宙 ``u`` で定数をインスタンス化することをLeanに指示する。

したがって、例えば、前節の例を等号関係に特化させることができる:

```lean
variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
```

射影表記(``Foo.bar e`` の ``e.bar`` という略記)も使うことができる:

```lean
# variable (α : Type) (a b c d : α)
# variable (hab : a = b) (hcb : c = b) (hcd : c = d)
example : a = d := (hab.trans hcb.symm).trans hcd
```

反射律 ``Eq.refl`` は見た目よりも強力である。Calculus of Constructionsにおいて、任意の型は計算可能な解釈を持ち、論理フレームワークは同一の簡約結果を持つ項たちを同じものとして扱うことを思い出してほしい。その結果、いくつかの非自明な恒等式を反射律によって証明することができる:

```lean
variable (α β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _
```

論理フレームワークのこの機能は非常に重要であるため、Leanのライブラリでは ``Eq.refl _`` により ``rfl`` という記法を定義している:

```lean
# variable (α β : Type)
example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
example (a : α) (b : β) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl
```

しかし、等号は同値関係以上のものである。等号は、左辺の式を右辺の式に置き換えても、あるいは右辺の式を左辺の式に置き換えても真理値が変わらないという意味で、全ての命題が等号によって主張される同値性を尊重するという重要な性質を持っている。つまり、``h1 : a = b`` と ``h2 : p a`` があれば、代入 ``Eq.subst h1 h2`` を使って ``p b`` の証明を作ることができる。

```lean
example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)  -- h2の型の中に登場するh1の左辺をh1の右辺で書き換える
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

example (α : Type) (a b : α) (p : α → Prop)  -- h2の型の中に登場するh1の右辺をh1の左辺で書き換える
    (h1 : a = b) (h2 : p b) : p a :=
  h1 ▸ h2
```

2番目、3番目の例の中の三角形は、``Eq.subst`` と ``Eq.symm`` の上に構築されたマクロで、``\t`` と打つことで入力できる。``h1 ▸ h2`` は「``h1`` を使って ``h2`` を書き換える」と解釈できる。

``Eq.subst`` 規則は、より明示的な置換を行う以下の補助規則を定義するために使われる。これらは関数適用項、つまり ``s t`` の形の項を扱うためのものである。具体的には、``congrArg`` は ``s`` を固定して ``t`` を置換するのに使われ、``congrFun`` は ``t`` を固定して ``s`` を置換するのに使われ、``congr`` は ``s`` と ``t`` の両方を一度に置換するのに使われる。

```lean
variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁
```

Leanのライブラリには次のような一般的な恒等式が多数収載されている:

```lean
variable (a b c : Nat)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c
```

``Nat.mul_add`` と ``Nat.add_mul`` はそれぞれ ``Nat.left_distrib`` と ``Nat.right_distrib`` の別名である。上記の性質は、自然数（``Nat`` 型）に関するものである。

```lean
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm
```

``Eq.subst`` の2番目の暗黙の引数は、置換が行われる文脈を提供するもので、``α → Prop`` 型を持っていることに注意してほしい。

```lean
#check Eq.subst  -- {α : Sort u} {motive : α → Prop} {a b : α} (h₁ : a = b) (h₂ : motive a) : motive b
```

したがって、この述語を推論するには、*higher-order unification*(高階ユニフィケーション)のインスタンス(高階単一子)が必要である。一般論として、高階単一子が存在するかを決定する問題は決定不能であり、Leanはせいぜいこの問題に対して不完全で近似的な解を提供することしかできない。そのため、``Eq.subst`` は必ずしも思い通りに動くとは限らない。マクロ ``h ▸ e`` はこの暗黙の引数を計算する際により効果的なヒューリスティクスを使う。そのため、``Eq.subst`` の適用が失敗するような状況でも、``h ▸ e`` が成功することがしばしばある。

等式の推論は非常に一般的で重要であるため、Leanはそれをより効率的に実行するためのメカニズムを数多く提供している。次の節では、より自然で簡潔な方法で計算的証明を書くための構文を提供する。しかし、より重要なのは、等式推論が*rewriter*(項書き換え器)、*simplifier*(単純化器)、その他の自動化によって成り立っていることである。項書き換え器と単純化器については次の節で簡単に説明し、次の章でさらに詳しく説明する。

## Calculational Proofs (計算的証明)

計算的証明は、等号の推移律などの基本原則によって構成される中間結果の連鎖にすぎない。Leanにおいて、計算的証明はキーワード ``calc`` から始まる以下の構文を持つ:

```
calc
  <expr>_0  'op_1'  <expr>_1  ':='  <proof>_1
  '_'       'op_2'  <expr>_2  ':='  <proof>_2
  ...
  '_'       'op_n'  <expr>_n  ':='  <proof>_n
```

``calc`` 以降の一連の行は全て同じインデントを持つ必要があることに注意。そうでなければコンパイルエラーになる。各 ``<proof>_i`` は ``<expr>_{i-1} op_i <expr>_i`` の証明である必要がある。

最初の行に ``calc <expr>_0`` と書いた後、その次の行から `_` を使う事もできる。これは関係命題と証明の組からなる行を揃えるのに便利である。

```
calc <expr>_0 
    '_' 'op_1' <expr>_1 ':=' <proof>_1
    '_' 'op_2' <expr>_2 ':=' <proof>_2
    ...
    '_' 'op_n' <expr>_n ':=' <proof>_n
```

次は計算的証明の一例である:

```lean
variable (a b c d e : Nat)
variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = 1 + d)

theorem T : a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4
```

この証明の書き方は、次章で詳しく説明する ``simp`` タクティクや ``rewrite`` タクティクと併用すると最も効果的である。例えば、``rewrite`` の略語 ``rw`` を使うと、上記の証明は次のように書ける:

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  calc
    a = b      := by rw [h1]
    _ = c + 1  := by rw [h2]
    _ = d + 1  := by rw [h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]
```

基本的に、``rw`` タクティクは ``[]`` でくくられた等式(前提、定理名、複合的な項のいずれでもよい)を用いてゴールを「書き換える」。その結果、ゴールが恒等式 ``t = t`` になったら、``rw`` タクティクは自動で反射律を使ってゴールを証明する。

段階的な書き換えを一度に実行することもできる。上の証明は次のように短縮できる:

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  calc
    a = d + 1  := by rw [h1, h2, h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]
```

ここまで短くしてもよい:

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  by rw [h1, h2, h3, Nat.add_comm, h4]
```

``simp`` タクティクは、ゴールの項の中に与えられた恒等式が適用できる場所がある限り、与えられた恒等式を任意の順番で繰り返し適用し、ゴールを書き換える。また、システム内で宣言された既存のルールも活用し、書き換えのループを避けるため可換性を賢く適用する。上記の証明は ``simp`` を使って次のように証明することもできる:

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  by simp [h1, h2, h3, Nat.add_comm, h4]
```

次の章では ``rw`` と ``simp`` の派生について説明する。

``calc`` コマンドは、何らかの形で推移律を持つあらゆる関係に対して使うことができる。計算的証明の中で異なる関係を組み合わせることもできる。

```lean
example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3
```

``Trans`` 型クラスの新しいインスタンスを追加することで、``calc`` に新しい推移律の定理を「教える」ことができる。型クラスは後で紹介するが、とりあえず以下に新しい ``Trans`` インスタンスを使って ``calc`` 記法を拡張する方法を示す小さな例を挙げる。

```lean
def divides (x y : Nat) : Prop :=
  ∃ k, k*x = y

def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  let ⟨k₂, d₂⟩ := h₂
  ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

def divides_mul (x : Nat) (k : Nat) : divides x (k*x) :=
  ⟨k, rfl⟩

instance : Trans divides divides divides where
  trans := divides_trans

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    divides x y     := h₁
    _ = z           := h₂
    divides _ (2*z) := divides_mul ..

infix:50 " ∣ " => divides

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    x ∣ y   := h₁
    _ = z   := h₂
    _ ∣ 2*z := divides_mul ..
```

上記の例から、ユーザーが定義した関係がinfix表記を持たなくても、その関係について ``calc`` が使えることがわかる。最後に、上記の例の縦棒 `∣` はunicodeのものである。``match ... with`` 式で使われるASCIIの ``|`` のオーバーロードを避けるためにunicodeの記号を用いた。

``calc`` を用いると、前節の証明をより自然にわかりやすく書くことができる。

```lean
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y  := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y                := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y)            := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y              := by rw [←Nat.add_assoc]
```

ここでは、``calc`` の他の記法を検討する価値がある。最初の式がこれだけ広いスペースをとる場合、最初の関係式に ``_`` を使うと、全ての関係式が自然に整列される:

```lean
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc (x + y) * (x + y)
    _ = (x + y) * x + (x + y) * y       := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y     := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y   := by rw [←Nat.add_assoc]
```

ここで、``Nat.add_assoc`` の前の左矢印は、書き換えの際に与えられた恒等式を逆向きに使うように ``rw`` に指示する(左矢印は ``\l`` と打つと入力できる。これと等価なascii文字列 ``<-`` を使ってもいい)。簡潔さを求めるなら、次のように単独の ``rw`` や ``simp`` を使うだけで証明を完結させることもできる。 

```lean
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]
```

## The Existential Quantifier (存在量化子)

最後に、存在量化子について考えよう。存在量化子は ``exists x : α, p x`` または ``∃ x : α, p x`` と書くことができる。どちらの記法も、Leanのライブラリで定義されている ``Exists (fun x : α => p x)`` という長ったらしい表現の便利な省略形である。

もうお分かりのように、Leanのライブラリは存在量化子の導入則と除去則を含んでいる。導入則は簡単である: ``∃ x : α, p x`` を証明するには、適切な項 ``t : α`` と ``p t`` の証明を与えればよい。次はその例である:

```lean
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

#check @Exists.intro  -- @Exists.intro : ∀ {α : Sort u_1} {p : α → Prop} (w : α), p w → Exists p
```

型が文脈から明らかな場合、``Exists.intro t h`` の代わりに、匿名コンストラクタ表記 ``⟨t, h⟩`` を使うことができる。

```lean
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩  -- ⟨y, hxy, hyz⟩ は ⟨y, ⟨hxy, hyz⟩ ⟩ と同じ
```

``Exists.intro`` には暗黙の引数があることに注意してほしい: Leanは結論 ``∃ x, p x`` から述語 ``p : α → Prop`` が何であるかを推論しなければならない。これは簡単なことではない。例えば、``hg : g 0 0 = 0`` とし、``Exists.intro 0 hg`` と書くとする。このとき、述語 ``p`` は 定理 ``∃ x, g x x = x``、``∃ x, g x x = 0``、``∃ x, g x 0 = x`` などに対応する様々な値を取りうる。Leanは文脈からどれが適切かを推論する。次の例では、``pp.explicit`` オプションを ``true`` に設定し、``#print`` コマンドに暗黙の引数を表示するように問い合わせている。

```lean
variable (g : Nat → Nat → Nat)
variable (hg : g 0 0 = 0)

theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true  -- 暗黙の引数を表示する
#print gex1
#print gex2
#print gex3
#print gex4
```

``Exists.intro`` は主張本体の証人(存在量化を受けた主張を満たす項)を隠すため、情報を隠す操作であると解釈することができる。存在量化子の除去則 ``Exists.elim`` はその逆の操作を行う。``Exists.elim`` は任意の値 ``w : α`` に対して ``p w`` ならば ``q`` が成立することを示すことで、``∃ x : α, p x`` から命題 ``q`` を証明することを可能にする。大雑把に言えば、``∃ x : α, p x`` が成立するなら ``p x`` を満たす ``x`` が存在することがわかるので、その ``x`` に名前、例えば ``w`` を与えることができる。もし ``q`` が ``w`` に言及していなければ、``q`` が ``p w`` から導かれることを示すことは、``q`` が ``p w`` を満たす ``x`` の存在から導かれることを示すことに等しい。次はその例である:

```lean
variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)

#check @Exists.elim  -- ∀ {α : Sort u_1} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (a : α), p a → b) → b
```

ここで、匿名コンストラクタ表記 ``⟨w, hw.right, hw.left⟩`` が入れ子になったコンストラクタの適用を省略していることに注意。``⟨w, hw.right, hw.left⟩`` は ``⟨w, ⟨hw.right, hw.left⟩⟩`` と書いたのと同じである。

存在量化子除去則と選言除去則を比較することは有用であろう: 主張 ``∃ x : α, p x`` は、 ``a`` が型 ``α`` の全ての項をわたるときの、命題 ``p a`` 全てを選言で繋げたものと考えることができる。

存在命題は、2章の従属型の節で説明したシグマ型(依存積型)に非常に似ていることに注目しよう。``a : α`` と ``h : p a`` が与えられたとき、項 ``Exists.intro a h`` は型 ``(∃ x : α, p x) : Prop`` を持つ一方で、``Sigma.mk a h`` は型 ``(Σ x : α, p x) : Type`` を持つ。この ``∃`` と ``Σ`` の類似性はカリー=ハワード同型のもう一つの例である。

```lean
section exist_prop
variable (a : α) (p : α → Prop) (h : p a)

#check Exists.intro a h  -- Exists p
end exist_prop

section sigma_type
variable (a : α) (p : α → Type) (h : p a)

#check Sigma.mk a h      -- Sigma p
end sigma_type
```

Leanは、``match`` 式を用いた、存在量化子を除去するためのより便利な方法を提供する:

```lean
variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩
```

``match`` 式はLeanの関数定義システムの一部であり、複雑な関数を定義する便利で表現力豊かな方法を提供する。再びカリー=ハワード同型により、この関数定義方法 ``match`` を証明の記述にも応用させることができる。``match`` 文は存在量化された主張を ``w`` と ``hw`` に「分解」する。これらは命題の証明記述内で使うことができる。より明確にするために、マッチで分解されてできた要素に型の注釈を付けることができる:

```lean
# variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩
```

match文を使って、存在量化子と連言を同時に分解することもできる:

```lean
# variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hpw : p w), (hqw : q w)⟩ => ⟨w, hqw, hpw⟩
```

Leanは ``let`` キーワードにもパターンマッチングを提供する:

```lean
# variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩
```

これは、基本的に上記の ``match`` 構文の代替表記に過ぎない。Leanでは、``fun`` キーワードの中で暗黙の ``match`` を使うこともできる:

```lean
# variable (α : Type) (p q : α → Prop)
example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
```

[8章 Induction and Recursion (帰納と再帰)](./induction_and_recursion.md) では、これらの派生構文は全てより一般的なパターンマッチング構文のインスタンスであることを説明する。

次の例では、``is_even a`` を ``∃ b, a = 2 * b`` と定義し、2つの偶数の和は偶数であることを示す。

```lean
def is_even (a : Nat) : Prop := ∃ b : Nat, a = 2 * b

theorem even_plus_even {a b : Nat} (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
    Exists.intro (w1 + w2)
      (calc a + b
        _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
        _ = 2 * (w1 + w2)   := by rw [Nat.mul_add])))

theorem even_plus_even2 : ∀ a b : Nat, is_even a → is_even b → is_even (a + b) :=
  fun a : Nat =>
  fun b : Nat => 
  fun ⟨(w1 : Nat), (hw1 : a = 2 * w1)⟩ =>
  fun ⟨(w2 : Nat), (hw2 : b = 2 * w2)⟩ =>
    have hw3 : a + b = 2 * (w1 + w2) :=
      calc a + b
        _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
        _ = 2 * (w1 + w2)   := by rw [Nat.mul_add]
    ⟨(w1 + w2 : Nat), (hw3 : a + b = 2 * (w1 + w2))⟩
```

マッチ文、匿名コンストラクタ、``rewrite`` タクティク……、この章で説明した様々な小道具を使ってこの証明を簡潔に書くと次のようになる:

```lean
# def is_even (a : Nat) := ∃ b, a = 2 * b
theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ => ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩
```

構成的(構成的論理の)「または」が古典的「または」よりも強いように、構成的「存在する」も古典的「存在する」より強い。次の例に挙げるような含意命題を証明するためには、古典論理的な推論を必要とする。なぜなら、構成的論理では、「全ての ``x`` が ``¬ p`` を満たす」の否定が真であることと、「``p`` を満たす ``x`` が存在する」が真であることは同じではないからである。

```lean
open Classical
universe u
variable (α : Sort u) (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x := ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)
```

以下に、練習問題として存在量化子を含む一般的な恒等式を挙げる。ここでは、できる限り多くの命題を証明することを勧める。また、どの命題が非構成的で、古典論理的な推論を必要とするかは、読者の判断に委ねる。

```lean
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := sorry
example (a : α) : r → (∃ x : α, r) := sorry
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
```

2番目の例と最後の2つの例は、型 ``α`` には少なくとも1つの要素 ``a`` が存在するという前提を必要とすることに注意してほしい。

以下は2つの難しい問題への解答である:

```lean
open Classical

variable (α : Type) (p q : α → Prop)
variable (a : α)
variable (r : Prop)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨a, (h1 : p a ∨ q a)⟩ =>
      Or.elim h1
        (fun hpa : p a => Or.inl ⟨a, hpa⟩)
        (fun hqa : q a => Or.inr ⟨a, hqa⟩))
    (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h
        (fun ⟨a, hpa⟩ => ⟨a, (Or.inl hpa)⟩)
        (fun ⟨a, hqa⟩ => ⟨a, (Or.inr hqa)⟩))

example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨b, (hb : p b → r)⟩ =>
     fun h2 : ∀ x, p x =>
     show r from hb (h2 b))
    (fun h1 : (∀ x, p x) → r =>
     show ∃ x, p x → r from
       byCases
         (fun hap : ∀ x, p x => ⟨a, fun h' : p a => h1 hap⟩)
         (fun hnap : ¬ ∀ x, p x =>
          byContradiction
            (fun hnex : ¬ ∃ x, p x → r =>
              have hap : ∀ x, p x :=
                fun x =>
                byContradiction
                  (fun hnp : ¬ p x =>
                    have hex : ∃ x, p x → r := ⟨x, (fun hp : p x => absurd hp hnp)⟩
                    show False from hnex hex)
              show False from hnap hap)))
```

## More on the Proof Language (証明言語の詳細)

``fun``、``have``、``show`` などのキーワードにより、非形式的な数学的証明の構造を反映した形式的証明項を書くことができることを見てきた。この節では、証明言語の他の便利な機能について説明する。

まず、ラベルを付けることなく補助ゴールを導入するために、無名の「have」式を使うことができる。``this`` キーワードを用いると、無名の「have」式を使って導入された最後の項を参照することができる:

```lean
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)
```

証明の中ではいくつもの事実を使い捨てることが多いので、ラベルの付いた項が増えすぎてごちゃごちゃするのを防ぐには無名の「have」式が有効である。

ゴール(今ここで使いたい項の型)が推論できる場合は、``by assumption`` と書くことでLeanに証明を埋めるよう頼むこともできる:

```lean
# variable (f : Nat → Nat)
# variable (h : ∀ x : Nat, f x ≤ f (x + 1))
example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
  show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)
```

``by assumption`` はLeanに ``assumption`` タクティクを使うように指示し、``assumption`` タクティクはローカルなコンテキストで適切な前提命題(の証明項)を見つけることでゴールを証明する。``assumption`` タクティクについては次の章で詳しく説明する。

``‹p›`` と書くことで、Leanに証明を埋めるよう頼むこともできる。ここで、``‹p›`` はLeanにコンテキストから証明を見つけてもらいたい命題である。この角ばった括弧はそれぞれ ``\f<`` と ``\f>`` と打つと入力できる。"f" は "フランス語" を意味する。なぜならこのunicode記号はフランス語における引用符としても使われるからである。この表記はLeanにおいて次のように定義されている:

```lean
notation "‹" p "›" => show p by assumption
```

このアプローチは、推論してほしい前提の型が明示的に与えられるため、``by assumption`` を用いるよりもロバストである。また、証明も読みやすくなる。以下は、より詳細な例である:

```lean
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  fun _ : f 0 ≥ f 1 =>
  fun _ : f 1 ≥ f 2 =>
  have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
  have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
  show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›
```

フランス語の引用符は、匿名で導入されたものだけでなくコンテキスト中の「あらゆるもの」を参照できることを覚えておこう。フランス語の引用符の適用範囲は命題だけにとどまらないが、これをデータに対して使うのはやや奇妙である:

```lean
example (n : Nat) : Nat := ‹Nat›
```

以降の章で、Leanのマクロシステムを使って証明言語を拡張する方法を紹介する。

## Exercises (練習問題)

1. 以下の命題を証明せよ:

```lean
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry
```

最後の例について、逆の命題が導出できないのはなぜかを理解してみよう。

2. 式の一部が全称量化された変数に依存しない場合、それを全称量化子の外側に持ってくることはしばしば可能である。以下の命題を証明してみよう(このうち2つ目の命題の1方向は古典論理を必要とする):

```lean
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := sorry
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry
```

3. 「理髪師のパラドックス」について考えてみよう。これは、ある町において、「自分で髭を剃らない男性全員の髭を剃り、自分で髭を剃る男性の髭は一切剃らない男性の理髪師がいる」という主張である。この主張が矛盾することを示せ:

```lean
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := sorry
```

4. パラメータを持たない ``Prop`` 型の項は(それが真か偽かを問わない)単なる主張である。まず以下の ``prime`` と ``Fermat_prime`` の定義を埋め、それらを使って他の定義を構築せよ。例えば、任意の自然数 ``n`` に対して、``n`` より大きな素数が存在すると主張することで、素数は無限に存在すると言うことができる。弱いゴールドバッハ予想は、5より大きい任意の奇数は3つの素数の和で表されることを主張している。必要であれば、フェルマー素数や他の記述の定義を調べてみよう。

```lean
def even (n : Nat) : Prop := sorry

def prime (n : Nat) : Prop := sorry

def infinitely_many_primes : Prop := sorry

def Fermat_prime (n : Nat) : Prop := sorry

def infinitely_many_Fermat_primes : Prop := sorry

def goldbach_conjecture : Prop := sorry

def Goldbach's_weak_conjecture : Prop := sorry

def Fermat's_last_theorem : Prop := sorry
```

5. 存在量化子の節で列挙した恒真式をできるだけ多く証明せよ。
