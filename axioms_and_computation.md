# Axioms and Computation (公理と計算)

Leanに実装された*Calculus of Constructions*には、依存関数型、帰納型、そして最下層にある*impredicative*(自己参照可能)で*proof-irrelevant*(証明無関係)な ``Prop`` 型から始まる宇宙の階層が含まれていることを見てきた。本章では、Leanに実装されている*Calculus of Inductive Constructions*(CIC)に公理と規則を追加して、CICを拡張する方法を考える。このような方法で基礎体系を拡張することは、多くの場合便利である。基礎体系を拡張することで、より多くの定理を証明することが可能になるか、そうでなければ以前は簡単に証明できなかった定理を簡単に証明できるようになる。しかし、公理を追加することで、その正しさ(無矛盾性)に関する懸念の増大以上の否定的な結果が生じることもある。特に、追加した公理の使用は、以下で紹介するように定義と定理の計算内容に影響する。

Leanは計算的推論と古典論理的推論の両方をサポートするように設計されている。望むなら、ユーザーは*computationally pure*(計算上純粋)なフラグメントだけを使うことができ、そうすればシステム内の全ての閉じた式が*canonical normal form*(正規標準形)に評価されることが保証される。特に、例えば ``Nat`` 型の計算上純粋な閉じた式は、全て数字に簡約される。

Leanの標準ライブラリでは、*propositional extensionality*(命題外延性)という追加の公理と、*function extensionality*(関数外延性)の原理を含意する*quotient*(商)の構築が定義されている。これらの公理の拡張は、例えば集合や有限集合の理論を開発するために利用される。これらの公理やそれらに依存する定理を使うと、Leanのカーネルにおける項評価がブロックされ、``Nat`` 型の閉項が数字に評価されなくなることがあることを以下で見る。しかし、これらの公理は新しい命題(の証明項)を(無条件に)追加するだけであり、Leanは仮想マシン評価器用のバイトコード(中間コード)に定義をコンパイルする際に型と命題の情報を消去するため、これらの公理は計算的解釈と両立する。計算に傾倒したユーザーであっても、計算における推論を行うために古典的な排中律を使いたいと思うかもしれない。排中律もカーネルでの項評価をブロックするが、排中律は定義のバイトコードへのコンパイルと両立する。

また、標準ライブラリは、計算的解釈とは全く相反する*choice principle*(選択原理)も定義している。選択原理は「データ(証明以外の項)」の存在を主張する命題から魔法のようにデータを生成することができ、便利だからである。いくつかの古典的な構文を使うには選択原理が必須であり、ユーザーは必要なときに選択原理をインポートすることができる。しかし、古典的な構文を使ってデータを生成する式は、計算可能な内容を持っていない。Leanでは、その事実を示すために、このような定義を ``noncomputable`` とマークする必要がある。

(*Diaconescu's theorem*として知られる)巧妙なトリックを使うと、命題外延性、関数外延性、選択原理から排中律を導くことができる。しかし、上述の通り、データを作るために使用されない限り、排中律や他の古典的な原理の使用はバイトコードコンパイルやコード抽出と両立する。(訳者注: 上記の公理たちに関して言えば、データを作るために古典的な原理を使用したときに限り計算不可能になる。)

要約すると、宇宙、依存関数型、帰納型という基本的なフレームワークの上に、標準ライブラリはさらに3つの公理を追加している:

- 命題外延性の公理 ``propext``
- 商型 ``Quot`` の構築 : 関数外延性 ``funext`` を含意する
- 選択原理 ``Classical.choice`` : 存在命題 ``Nonempty α`` からデータ ``a : α`` を生成する

ここで、最初の2つはLeanにおける項の正規化をブロックするが、バイトコード評価とは両立する。一方で、3つ目は計算的に解釈することができない。以下でこれらの詳細について述べる。

## Historical and Philosophical Context (歴史的文脈と哲学的文脈)

数学の歴史の大半において、数学は本質的に計算可能なものであった: 幾何学は幾何学的なオブジェクトの作図を扱い、代数学は連立方程式の計算可能な解法と関係があり、解析学は時間発展する物理系の将来の振る舞いを計算する手段を提供した。「任意の ``x`` について、...を満たす ``y`` が存在する(``∀ x, ∃ y, ...``)」という定理の証明から、``x`` が与えられたときにそのような ``y`` を計算するアルゴリズムを抽出するのは、一般的に簡単なことだった。

しかし、19世紀になり数学的議論の複雑さが増すと、数学者たちはアルゴリズム的情報を必須としない、数学的対象の具体的な表現方法の詳細を抽象化した数学的対象の記述を使う新たな推論様式を開発した。その目的は計算の細部に拘泥することなく強力な「概念的」理解を得ることだったが、結果として直観的で計算可能な体系では単に**偽**である数学的定理を認めることになった。

今日においても、計算が数学にとって重要であることはほとんど一律に合意されている。しかし、計算にまつわる問題にどのように対処するのが最善かについては、様々な見解がある。*constructive*(構成的)な観点からすれば、数学をその計算的ルーツから切り離すのは間違いである: 全ての意味のある数学の定理は、直観的で計算的な解釈を持つべきである。*classical*(古典的)な観点からすると、問題の分離を維持した方が有益である: 私たちは、プログラムについて推論するために非構成的な理論やメソッドを使う自由を維持しながら、コンピュータプログラムを書くためにある言語と付属するメソッドを使うことができる。Leanは構成的アプローチと古典的アプローチの両方をサポートするように設計されている。ライブラリのコア部分は構成的に開発されている(そのため古典的な原理を使わない選択ができる)が、システムは古典的な数学的推論を行うためのサポートも提供している。

依存型理論の最も計算上純粋な部分は ``Prop`` 型の使用を完全に避けている。帰納型と依存関数型はデータ型とみなすことができ、これらの型の項は、これ以上簡約規則を適用できなくなるまで簡約規則を適用することで「評価」することができる。原理的には、``Nat`` 型の任意の閉項(自由変数を持たない項)は ``succ (succ (... (succ zero)...))`` という数字に評価されるはずである。

証明無関係な ``Prop`` 型を導入し、定理に ``irreducible`` とマークすることは、問題分離への第一歩である。このマークの意図は、型 ``p : Prop`` の項は計算において何の役割も果たすべきでないということであり、その意味で項 ``t : p`` の具体的な構成は計算に「無関係」である。``Prop`` 型の項を組み込んだ計算可能オブジェクトを定義することはできる。ポイントは、``Prop`` 型の項は「計算結果を推論」する役に立つが、項から「コードを抽出」するときには無視できるということである。しかし、``Prop`` 型の項はまったく無害というわけではない。``Prop`` 型の項には任意の型 ``α`` とその項 ``s : α``、``t : α`` に対する等式 ``s = t : Prop`` が含まれる。このような等式は項を型チェックするためにキャストとして使用される。以下では、このようなキャストがどのようにシステム内の計算をブロックしうるかの例を見ていく。しかし、命題の内容を消去し、中間の型付け制約を無視し、正規形に達するまで項を簡約する評価枠組みの中では、計算は依然として可能である。これはまさにLeanの仮想マシンが行っていることである。

証明無関係な ``Prop`` を採用した場合、任意の命題 ``p`` に対する排中律 ``p ∨ ¬p`` を使うことは正当だと考えるかもしれない。もちろん、排中律がCICの規則に従って計算をブロックする可能性はあるが、上述のようにバイトコードの評価をブロックすることはない。Leanの基礎的理論において、計算に無関係な証明と計算に関係するデータの区別を完全に消し去り、データを計算不可能にするのは、節[Choice (選択原理)](#choice-選択原理)で説明する選択原理だけである。

## Propositional Extensionality (命題外延性)

命題外延性は次のような公理である:

```lean
# namespace Hidden
axiom propext {a b : Prop} : (a ↔ b) → a = b
# end Hidden
```

``propext`` は、2つの命題が互いを含意するとき、それらは実際に等しいと主張する公理である。これは命題の集合論的な解釈と一致する。命題の集合論的な解釈において、``a : Prop`` は空であるか、互いに区別されたある元 ``*`` のみを含むシングルトン ``{*}`` である。この公理は、どのようなコンテキストでも命題をそれと同値な命題に置き換えることができるという効果を持つ:

```lean
theorem thm₁ (a b c d e : Prop) (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
  propext h ▸ Iff.refl _

theorem thm₂ (a b : Prop) (p : Prop → Prop) (h : a ↔ b) (h₁ : p a) : p b :=
  propext h ▸ h₁

#print axioms thm₁  -- 'thm₁' depends on axioms: [propext]
#print axioms thm₂  -- 'thm₂' depends on axioms: [propext]
```

<!--
最初の定理は、命題結合子が命題の同値性を保存するという事実を使えば、手間はかかるが ``propext`` なしで証明することができる。2番目の定理はより本質的な ``propext`` の使い方である。実際、2番目の定理は ``propext`` 自体と同値である。

定義や定理が与えられたとき、コマンド ``#print axioms`` を使うと、それらがどの公理に依存しているかを表示させることができる。

.. code-block:: lean

    variables a b c d e : Prop
    variable p : Prop → Prop

    theorem thm₁ (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
    propext h ▸ iff.refl _

    theorem thm₂ (h : a ↔ b) (h₁ : p a) : p b :=
    propext h ▸ h₁

    -- BEGIN
    #print axioms thm₁  -- propext
    #print axioms thm₂  -- propext
    -- END
-->

## Function Extensionality (関数外延性)

命題外延性と同様に、関数外延性は、全ての入力に対して出力が一致する ``(x : α) → β x`` 型の2つの関数は等しいことを主張する。

```lean
universe u v
#check (@funext :
           {α : Type u}
         → {β : α → Type u}
         → {f g : (x : α) → β x}
         → (∀ (x : α), f x = g x)
         → f = g)

#print funext
```

古典的な集合論の観点からは、2つの関数が等しいというのはまさにこのことを意味する([eqfnfv - Metamath Proof Explorer](https://us.metamath.org/mpeuni/eqfnfv.html))。これは関数の「外延的な」見方として知られている。しかし、構成的な観点からは、関数をアルゴリズム、あるいは何らかの明示的な方法で提示されるコンピュータプログラムと考える方が自然な場合もある。2つのコンピュータプログラムが、構文的には全く異なっているにも関わらず、全ての入力に対して同じ答えを計算できるという例は確かにある。同様に、同じ入出力動作をする2つの関数を同一視することを強制しないような関数の見方を維持したいと思うかもしれない。これは関数の「内包的な」見方として知られている。

関数外延性は商の存在から導かれる。この事実については次の節で説明する。実際、Leanの標準ライブラリでは、``funext`` は[商の構築から証明されている](https://github.com/leanprover/lean4/blob/master/src/Init/Core.lean)。

``α : Type`` に対して、``α`` の部分集合の型を表す ``Set α := α → Prop`` を定義したとする。つまり、部分集合と述語を本質的に同一視するとする。``funext`` と ``propext`` を組み合わせることで、このような集合の「外延性の定理」``setext`` が得られる:

```lean
def Set (α : Type u) := α → Prop

namespace Set

def mem (x : α) (a : Set α) : Prop := a x

infix:50 (priority := high) "∈" => mem

theorem setext {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))

theorem setext' {a b : Set α} (h : ∀ (x : α), a x ↔ b x) : a = b :=
  funext (fun x => propext (h x))

end Set
```

それから、例えば空集合や集合の共通部分を定義し、集合に関する恒等式を証明することができる:

```lean
# def Set (α : Type u) := α → Prop
# namespace Set
# def mem (x : α) (a : Set α) := a x
# infix:50 (priority := high) "∈" => mem
# theorem setext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
#   funext (fun x => propext (h x))
def empty : Set α := fun x => False

notation (priority := high) "∅" => empty

def inter (a b : Set α) : Set α :=
  fun x => x ∈ a ∧ x ∈ b

infix:70 " ∩ " => inter

theorem inter_self (a : Set α) : a ∩ a = a :=
  setext fun x => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => ⟨h, h⟩)

theorem inter_empty (a : Set α) : a ∩ ∅ = ∅ :=
  setext fun x => Iff.intro
    (fun ⟨_, h⟩ => h)
    (fun h => False.elim h)

theorem empty_inter (a : Set α) : ∅ ∩ a = ∅ :=
  setext fun x => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => False.elim h)

theorem inter.comm (a b : Set α) : a ∩ b = b ∩ a :=
  setext fun x => Iff.intro
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
# end Set
```

以下は、Leanのカーネル内部で関数外延性がどのように計算をブロックするかの一例である。

```lean
def f (x : Nat) := x
def g (x : Nat) := 0 + x

theorem f_eq_g : f = g :=
  funext fun x => (Nat.zero_add x).symm

def val : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) f_eq_g 0

-- does not reduce to 0
#reduce val

-- evaluates to 0
#eval val
```

まず、関数外延性を用いて2つの関数 ``f`` と ``g`` が等しいことを示す。次に ``0`` の型 ``Nat`` の中に登場する ``f`` を ``g`` に置き換えて ``0`` をキャストする。もちろん ``Nat`` は ``f`` に依存しないので、このキャストは実質的に何もしない。しかし、計算をブロックするにはこれで十分である: このシステムの計算規則の下で、数字に簡約されない ``Nat`` の閉項 ``val`` を手に入れた。今回の場合、``val`` を ``0`` に簡約してほしいと思うかもしれない。しかし、自明でない例では、このようなキャストを除去すると項の型が変わり、周囲の式の型が不正確になる可能性がある。しかしながら、仮想マシンは何の問題もなく ``val`` を ``0`` に評価できる。次は ``propext`` がどのように計算をブロックするかを示す、上と似た作為的な例である。

```lean
theorem tteq : (True ∧ True) = True :=
  propext (Iff.intro (fun ⟨h, _⟩ => h) (fun h => ⟨h, h⟩))

def val : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) tteq 0

-- does not reduce to 0
#reduce val

-- evaluates to 0
#eval val
```

*observational type theory*や*cubical type theory*を含む現在の型理論の研究プログラムは、関数外延性や商などを含む型キャストに対する簡約を許可する方法で型理論を拡張することを目指している。しかし、解決策はそれほど明確ではなく、Leanの基礎となるcalculusの規則はそのようなキャストの簡約を認めていない。

しかしながらある意味では、キャストは式の意味を変えるものではない。むしろ、キャストは式の型を推論するためのメカニズムだと言える。適切な意味論が与えられれば、簡約前後で型付けの正しさを保存するために必要な中間的な記録を無視して、項の意味を保持するやり方で項を簡約することは理にかなっている。

簡約可能性について、``Prop`` に新しい公理を追加することは問題にならない。証明無関係により、``Prop`` の項は何の情報も持たない。したがって、簡約手続きにおいて ``Prop`` の項は安全に無視できる。

## Quotients (商)

``α`` を任意の型とし、``r`` を ``α`` 上の同値関係とする。数学において、*quotient*(商) ``α / r``、つまり「``α`` の項の ``r`` による同値類」全体からなる型を作ることは一般的である。集合論的には、``α / r`` を ``α`` の項の ``r`` による同値類全体からなる集合とみなすことができる。このとき、``∀ a b, r a b → f a = f b`` を満たすという意味で同値関係を尊重する任意の関数 ``f : α → β`` を、各同値類 ``⟦x⟧`` に対して ``f' ⟦x⟧ = f x`` で定義される関数 ``f' : α / r → β`` に「持ち上げる」ことができる。Leanの標準ライブラリは、まさにこのような構築を実行する定数(公理)をいくつか追加することで、*Calculus of Constructions*を拡張している。そして、これらの最後の公理 ``Quot.lift`` をdefinitionalな除去則として導入している。

最も基本的な形では、商の構築 ``Quot.mk`` は ``r`` が同値関係であることさえ要求しない。Leanには以下の定数(公理)がビルトインに(ライブラリの最初のファイル ``Init.Prelude`` より先に)定義されている:

```lean
# namespace Hidden
universe u v

axiom Quot : {α : Sort u} → (α → α → Prop) → Sort u

axiom Quot.mk : {α : Sort u} → (r : α → α → Prop) → α → Quot r

axiom Quot.ind :
    ∀ {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop},
      (∀ a, β (Quot.mk r a)) → (q : Quot r) → β q

axiom Quot.lift :
    {α : Sort u} → {r : α → α → Prop} → {β : Sort u} → (f : α → β)
    → (∀ a b, r a b → f a = f b) → Quot r → β
# end Hidden
```

最初の公理 ``Quot`` は、型 ``α`` と ``α`` 上の二項関係 ``r`` が与えられたときに型 ``Quot r`` を形成する。2つ目の公理 ``Quot.mk`` は、``α`` の項を ``Quot r`` の項に写すもので、``r : α → α → Prop`` と ``a : α`` があれば、``Quot.mk r a`` は ``Quot r`` の項である。3つ目の公理 ``Quot.ind`` は、全ての ``Quot r`` の項が ``Quot.mk r a`` の形をとることを示す(``Quot r → Prop`` を ``Set (Quot r)`` とみなすと分かりやすい)。4つ目の公理 ``Quot.lift`` は、関数 ``f : α → β`` が与えられたとき、``h`` が「``f`` は関係 ``r`` を尊重する」ことの証明であれば、``Quot.lift f h`` は ``f`` に対応する ``Quot r`` 上の関数であることを主張する。この考え方は、``h`` が「``f`` はwell-definedである」ことを示す証明なら、関数 ``Quot.lift f h`` は ``α`` の各項 ``a`` について、``Quot.mk r a`` (``a`` を含む ``r``-(同値)類)を ``f a`` に写す、というものである。以下の証明で明らかなように、計算原理 ``Quot.Lift`` は除去則として宣言されている。

```lean
def mod7Rel (x y : Nat) : Prop :=
  x % 7 = y % 7

-- 商型 `Quot mod7Rel`
#check (Quot mod7Rel : Type)

-- `4` を含む `mod7Rel`-(同値)類
#check (Quot.mk mod7Rel 4 : Quot mod7Rel)

def f (x : Nat) : Bool :=
  x % 7 = 0

theorem f_respects (a b : Nat) (h : mod7Rel a b) : f a = f b := by
  simp [mod7Rel, f] at *
  rw [h]

def f' (x : Quot mod7Rel) : Bool :=
  Quot.lift f f_respects x

#check (f' : Quot mod7Rel → Bool)

-- 計算原理
example (a : Nat) : f' (Quot.mk mod7Rel a) = f a :=
  rfl
```

4つの定数(公理) ``Quot``、``Quot.mk``、``Quot.ind``、``Quot.lift`` 自体はあまり強くない。``Quot r`` を単に ``α`` とみなし、``Quot.lift`` を(``h`` を無視して) ``α → β`` 上の恒等関数とみなせば、``Quot.ind`` が満たされることが確認できる。そのため、これら4つの公理は追加の公理とはみなさない。

```lean
# variable (α β : Type)
# variable (r : α → α → Prop)
# variable (a : α)
# variable (f : α → β)
# variable (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂)
theorem thm : Quot.lift f h (Quot.mk r a) = f a := rfl

#print axioms thm   -- 'thm' does not depend on any axioms
```

これら4つの公理は、帰納型や帰納型に関連するコンストラクタと再帰子と同様に、*logical framework*(論理フレームワーク)の一部とみなされる。

``Quot`` を正真正銘の商にするのは、次の追加公理 ``Quot.sound`` である:

```lean
# namespace Hidden
# universe u v
axiom Quot.sound :
      ∀ {α : Type u} {r : α → α → Prop} {a b : α},
        r a b → Quot.mk r a = Quot.mk r b
# end Hidden
```

これは「``α`` の任意の2つの項は、``r`` によって関係しているなら、商の中で同一視される」と主張する公理である。定義や定理 ``foo`` が ``Quot.sound`` を使っている場合、コマンド ``#print axioms foo`` は ``Quot.sound`` を表示する。

もちろん、商の構築は ``r`` が同値関係である場合に最もよく使われる。上記のように ``r`` が与えられたとき、``r' a b`` と ``Quot.mk r a = Quot.mk r b`` が同値になるように ``r'`` を定義すれば、``r'`` が同値関係であることは明らかである。実際、``r'`` は関数 ``a ↦ quot.mk r a`` の*kernel*(核)である。公理 ``Quot.sound`` は、``r a b`` が ``r' a b`` を含意すると主張している。``Quot.lift`` と ``Quot.ind`` を使えば、「``r`` を含む任意の同値関係 ``r''`` に対して、``r' a b`` は ``r'' a b`` を含意する」という意味で、``r'`` が ``r`` を含む最小の同値関係であることを証明できる。特に、``r`` がそもそも同値関係であったならば、任意の ``a`` と ``b`` に対して、``r a b`` と ``r' a b`` が同値であることが証明できる。

同値関係や商の一般的なユースケースをサポートするために、標準ライブラリは*setoid*という概念を定義している。これは単に同値関係を持つ型である:

```lean
# namespace Hidden
class Setoid (α : Sort u) where
  r : α → α → Prop
  iseqv : Equivalence r

instance {α : Sort u} [Setoid α] : HasEquiv α :=
  ⟨Setoid.r⟩

namespace Setoid

variable {α : Sort u} [Setoid α]

theorem refl (a : α) : a ≈ a :=
  iseqv.refl a

theorem symm {a b : α} (hab : a ≈ b) : b ≈ a :=
  iseqv.symm hab

theorem trans {a b c : α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  iseqv.trans hab hbc

end Setoid
# end Hidden
```

型 ``α``、``α`` 上の二項関係 ``r``、``r`` が同値関係であることの証明 ``p`` が与えられたとき、``Setoid.mk r p`` により ``Setoid`` クラスのインスタンスを定義することができる。

```lean
# namespace Hidden
def Quotient {α : Sort u} (s : Setoid α) :=
  @Quot α Setoid.r
# end Hidden
```

定数(公理) ``Quotient.mk``、``Quotient.ind``、``Quotient.lift``、``Quotient.sound`` は ``Quot`` の対応する要素の特殊化に他ならない。型クラス推論が型 ``Setoid α`` のインスタンスを見つけることができるという事実は、多くの利点をもたらす。まず、``Setoid.r a b`` を ``a ≈ b`` (``\approx`` と打つと入力できる)と略記することができる。ここで、``Setoid.r`` という表記について、``Setoid`` のインスタンスが暗黙の引数となっていることに注意してほしい。また、``Setoid.refl``、``Setoid.symm``、``Setoid.trans`` という一般的な定理を使って同値関係に関する推論を行うことができる。商においては特に ``Quot.mk Setoid.r a`` の一般的な略記 ``⟦a⟧`` を使うことができる。ここでも ``Setoid.r`` 表記に関して ``Setoid`` のインスタンスが暗黙の引数となっている。``Quotient.exact`` という定理もある:

```lean
# universe u
#check (@Quotient.exact :
         ∀ {α : Sort u} {s : Setoid α} {a b : α},
           Quotient.mk s a = Quotient.mk s b → a ≈ b)
```

``Quotient.exact`` と ``Quotient.sound`` を組み合わせると、``Quotient s`` の各項が ``α`` の項の各同値類と正確に対応することが導かれる。

標準ライブラリでは、型 ``α × β`` は型 ``α`` と ``β`` の直積を表すことを思い出してほしい。商の使い方を説明するために、型 ``α`` の項からなる**非順序**対の型を、型 ``α × α`` の商として定義してみよう。まず、関連する同値関係を定義する:

```lean
private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

infix:50 " ~ " => eqv
```

次のステップは、``eqv`` が実際に同値関係であること、つまり反射的、対称的、推移的であることを証明することである。依存パターンマッチングを使って場合分けし、仮説を分解し、それを組み立てて結論を出すことで、便利で読みやすい方法でこれら3つの事実を証明することができる。

```lean
# private def eqv (p₁ p₂ : α × α) : Prop :=
#   (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
# infix:50 " ~ " => eqv
private theorem eqv.refl (p : α × α) : p ~ p :=
  Or.inl ⟨rfl, rfl⟩

private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
    Or.inr (by simp_all)

private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inl (by simp_all)

private theorem is_equivalence : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
```

``eqv`` が同値関係であることが証明されたので、``Setoid (α × α)`` のインスタンスを構築することができ、``Setoid (α × α)`` を使って非順序対の型 ``UProd α`` を定義することができる。

```lean
# private def eqv (p₁ p₂ : α × α) : Prop :=
#   (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
# infix:50 " ~ " => eqv
# private theorem eqv.refl (p : α × α) : p ~ p :=
#   Or.inl ⟨rfl, rfl⟩
# private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
#   | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
#     Or.inr (by simp_all)
# private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inl (by simp_all)
# private theorem is_equivalence : Equivalence (@eqv α) :=
#   { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
instance uprodSetoid (α : Type u) : Setoid (α × α) where
  r     := eqv
  iseqv := is_equivalence

def UProd (α : Type u) : Type u :=
  Quotient (uprodSetoid α)

namespace UProd

def mk {α : Type} (a₁ a₂ : α) : UProd α :=
  Quotient.mk' (a₁, a₂)

notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂

end UProd
```

非順序対 ``Quotient.mk (a₁, a₂)`` に対する略記 ``{a₁, a₂}`` をローカルに定義していることに注意してほしい。この略記は説明を目的とするなら便利であるが、レコードや集合のような対象を表すのに波括弧を使いにくくなるので、一般的には良いアイデアではない。

既に ``(a₁, a₂) ~ (a₂, a₁)`` を証明してあるので、``Quot.sound`` を使うことで ``{a₁, a₂} = {a₂, a₁}`` を簡単に証明することができる。

```lean
# private def eqv (p₁ p₂ : α × α) : Prop :=
#   (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
# infix:50 " ~ " => eqv
# private theorem eqv.refl (p : α × α) : p ~ p :=
#   Or.inl ⟨rfl, rfl⟩
# private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
#   | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
#     Or.inr (by simp_all)
# private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inl (by simp_all)
# private theorem is_equivalence : Equivalence (@eqv α) :=
#   { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
# instance uprodSetoid (α : Type u) : Setoid (α × α) where
#   r     := eqv
#   iseqv := is_equivalence
# def UProd (α : Type u) : Type u :=
#   Quotient (uprodSetoid α)
# namespace UProd
# def mk {α : Type} (a₁ a₂ : α) : UProd α :=
#   Quotient.mk' (a₁, a₂)
# notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂
theorem mk_eq_mk (a₁ a₂ : α) : {a₁, a₂} = {a₂, a₁} :=
  Quot.sound (Or.inr ⟨rfl, rfl⟩)
# end UProd
```

この例を完成させるため、``a : α`` と ``u : UProd α`` に対して、``a`` が非順序対 ``u`` の要素の1つである場合に成立する命題 ``a ∈ u`` を定義する。まず、順序対に対して同じような命題 ``mem_fn a u`` を定義する。次に ``mem_fn`` が同値関係 ``eqv`` を尊重することを補題 ``mem_respects`` で示す。これはLeanの標準ライブラリで広く使われているイディオムである。

```lean
# private def eqv (p₁ p₂ : α × α) : Prop :=
#   (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
# infix:50 " ~ " => eqv
# private theorem eqv.refl (p : α × α) : p ~ p :=
#   Or.inl ⟨rfl, rfl⟩
# private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
#   | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
#     Or.inr (by simp_all)
# private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inl (by simp_all)
# private theorem is_equivalence : Equivalence (@eqv α) :=
#   { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
# instance uprodSetoid (α : Type u) : Setoid (α × α) where
#   r     := eqv
#   iseqv := is_equivalence
# def UProd (α : Type u) : Type u :=
#   Quotient (uprodSetoid α)
# namespace UProd
# def mk {α : Type} (a₁ a₂ : α) : UProd α :=
#   Quotient.mk' (a₁, a₂)
# notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂
# theorem mk_eq_mk (a₁ a₂ : α) : {a₁, a₂} = {a₂, a₁} :=
#   Quot.sound (Or.inr ⟨rfl, rfl⟩)
private def mem_fn (a : α) : α × α → Prop
  | (a₁, a₂) => a = a₁ ∨ a = a₂

-- auxiliary lemma for proving mem_respects
private theorem mem_swap {a : α} :
      ∀ {p : α × α}, mem_fn a p = mem_fn a (⟨p.2, p.1⟩)
  | (a₁, a₂) => by
    apply propext
    apply Iff.intro
    . intro
      | Or.inl h => exact Or.inr h
      | Or.inr h => exact Or.inl h
    . intro
      | Or.inl h => exact Or.inr h
      | Or.inr h => exact Or.inl h


private theorem mem_respects
      : {p₁ p₂ : α × α} → (a : α) → p₁ ~ p₂ → mem_fn a p₁ = mem_fn a p₂
  | (a₁, a₂), (b₁, b₂), a, Or.inl ⟨a₁b₁, a₂b₂⟩ => by simp_all
  | (a₁, a₂), (b₁, b₂), a, Or.inr ⟨a₁b₂, a₂b₁⟩ => by simp_all; apply mem_swap

def mem (a : α) (u : UProd α) : Prop :=
  Quot.liftOn u (fun p => mem_fn a p) (fun p₁ p₂ e => mem_respects a e)

infix:50 (priority := high) " ∈ " => mem

theorem mem_mk_left (a b : α) : a ∈ {a, b} :=
  Or.inl rfl

theorem mem_mk_right (a b : α) : b ∈ {a, b} :=
  Or.inr rfl

theorem mem_or_mem_of_mem_mk {a b c : α} : c ∈ {a, b} → c = a ∨ c = b :=
  fun h => h
# end UProd
```

利便性のため、標準ライブラリは2変数関数を「持ち上げる」ための ``Quotient.lift₂`` と、2変数帰納法のための ``Quotient.ind₂`` も定義している。

最後に、なぜ商の構築が関数外延性を含意するのかについて、いくつかのヒントを示してこの節を締めくくる。型 ``(x : α) → β x`` を持つ関数の外延性等式が同値関係であることを示すのは難しくない。したがって、「同値関係を足した」依存関数型 ``extfun α β`` を考えることができる。もちろん、関数適用は ``f₁`` と ``f₂`` が同値関係にあるなら、``f₁ a`` は ``f₂ a`` と等しいという意味で、同値関係を尊重する。したがって、関数適用は関数 ``extfun_app : extfun α β → (x : α) → β x`` に持ち上げられる。しかし、任意の ``f`` について、``extfun_app ⟦f⟧`` は ``fun x => f x`` とdefinitionally equalであり、結果として ``f`` とdefinitionally equalである。したがって、``f₁`` と ``f₂`` が外延的に等しいとき、次のような等号の連鎖が成り立つ:

```
    f₁ = extfun_app ⟦f₁⟧ = extfun_app ⟦f₂⟧ = f₂
```

結果として、``f₁`` と ``f₂`` は等しい。

## Choice (選択原理)

標準ライブラリで定義されている最後の公理(選択原理)を述べるには、次のように定義される ``Nonempty`` 型が必要である:

```lean
# namespace Hidden
class inductive Nonempty (α : Sort u) : Prop where
  | intro (val : α) : Nonempty α
# end Hidden
```

``Nonempty α`` 型は ``Prop`` 型を持ち、そのコンストラクタはデータを含むので、[Inductively Defined Propositions (帰納的に定義された命題)](./inductive_types.md#inductively-defined-propositions-帰納的に定義された命題)の節で見た通り、``Nonempty α`` 型を除去しても命題を作ることしかできない。実際、``Nonempty α`` は ``∃ x : α, True`` と同値である:

```lean
example (α : Type u) : Nonempty α ↔ ∃ x : α, True :=
  Iff.intro (fun ⟨a⟩ => ⟨a, trivial⟩) (fun ⟨a, h⟩ => ⟨a⟩)
```

Lean版の選択公理は次のようにシンプルに表現される:

```lean
# namespace Hidden
# universe u
axiom choice {α : Sort u} : Nonempty α → α
# end Hidden
```

「``α`` は空でない」ことの証明 ``h`` さえあれば、``choice h`` は魔法のように ``α`` の項を生成する。もちろん、``choice`` の使用は意味のある計算をブロックする: 証明無関係の考え方の下では、``h`` はそのような項を見つける方法に関する情報を全く含んでいない。

``choice`` は ``Classical`` という名前空間の中にあるため、この公理のフルネームは ``Classical.choice`` である。選択原理は*indefinite description*(不定的記述)の原理と同値である。不定的記述の原理は*subtypes*(部分型)を使って次のように表すことができる:

```lean
# namespace Hidden
# universe u
# axiom choice {α : Sort u} : Nonempty α → α
noncomputable def indefiniteDescription {α : Sort u} (p : α → Prop)
                                        (h : ∃ x, p x) : {x // p x} :=
  choice <| let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩
# end Hidden
```

この定義は ``choice`` に依存するため、Leanは ``indefiniteDescription`` のバイトコードを生成できない。したがって、この定義を ``noncomputable`` とマークする必要がある。また、``Classical`` 名前空間では、関数 ``choose`` とプロパティ ``choose_spec`` は ``indefiniteDescription`` の(2つの要素からなる)出力を分解し、各要素を抽出する:

```lean
# open Classical
# namespace Hidden
noncomputable def choose {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α :=
  (indefiniteDescription p h).val

theorem choose_spec {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : p (choose h) :=
  (indefiniteDescription p h).property
# end Hidden
```

また、選択原理 ``Choice`` は「空でない」という性質 ``Nonempty`` と「有項である」というより構成的な性質 ``Inhabited`` の区別をなくしてしまう:

```lean
# open Classical
theorem inhabited_of_nonempty : Nonempty α → Inhabited α :=
  fun h => choice (let ⟨a⟩ := h; ⟨⟨a⟩⟩)
```

次節では ``propext``、``funext``、``choice`` の3つを合わせると、排中律と任意の命題の決定可能性が導かれることを説明する。これらを用いると、不定的記述の原理を次のように強化することができる:

```lean
# open Classical
# universe u
#check (@strongIndefiniteDescription :
         {α : Sort u} → (p : α → Prop)
         → Nonempty α → {x // (∃ (y : α), p y) → p x})
```

前提となる型 ``α`` が空でないとすると、``p`` を満たす項が存在するなら、``strongIndefiniteDescription p`` は ``p`` を満たす項 ``x`` を生成する(``p`` を満たす項が存在しないなら、``strongIndefiniteDescription p`` は ``choice`` により生成された型 ``α`` の任意の項を返す)。この関数 ``strongIndefiniteDescription`` の出力から値要素を抽出する関数は*Hilbert's epsilon function*(ヒルベルトのε関数)として知られている:

```lean
# open Classical
# universe u
#check (@epsilon :
         {α : Sort u} → [Nonempty α]
         → (α → Prop) → α)

#check (@epsilon_spec :
         ∀ {α : Sort u} {p : α → Prop} (hex : ∃ (y : α), p y),
           p (@epsilon _ (nonempty_of_exists hex) p))
```

関数 ``epsilon_spec`` は、``p`` を満たす項が存在するという証明を受け取ると、``p (epsilon p)`` の証明を返す。

## The Law of the Excluded Middle (排中律)

排中律は次のように表現される:

```lean
open Classical

#check (@em : ∀ (p : Prop), p ∨ ¬p)
```

[Diaconescuの定理](http://en.wikipedia.org/wiki/Diaconescu%27s_theorem)は、選択公理から排中律が導かれることを述べている。より正確には、Diaconescuの定理は、``Classical.choice``、``propext``、``funext`` から排中律が導かれることを示している。以下に標準ライブラリにあるDiaconescuの定理の証明を記す。

まず、必要な公理をインポートして、2つの述語 ``U`` と ``V`` を定義する:

```lean
# namespace Hidden
open Classical
theorem em (p : Prop) : p ∨ ¬p :=
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p

  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
#   sorry
# end Hidden
```

もし ``p`` が真なら、``Prop`` 型の任意の項は ``U`` と ``V`` の両方に属する。もし ``p`` が偽なら、``U`` はシングルトン ``true`` であり、``V`` はシングルトン ``false`` である。

次に、``choose`` を使って ``U`` の元と ``V`` の元を1つ選ぶ:

```lean
# namespace Hidden
# open Classical
# theorem em (p : Prop) : p ∨ ¬p :=
#   let U (x : Prop) : Prop := x = True ∨ p
#   let V (x : Prop) : Prop := x = False ∨ p
#   have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
#   have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
  let u : Prop := choose exU
  let v : Prop := choose exV

  have u_def : U u := choose_spec exU
  have v_def : V v := choose_spec exV
#   sorry
# end Hidden
```

``U`` と ``V`` はそれぞれ選言命題なので、``u_def`` と ``v_def`` の組は計4つのケースを表している。これらのケースのうち1つでは ``u = True`` かつ ``v = False`` であり、他の全てのケースでは ``p`` が真である。したがって、次のようになる:

```lean
# namespace Hidden
# open Classical
# theorem em (p : Prop) : p ∨ ¬p :=
#   let U (x : Prop) : Prop := x = True ∨ p
#   let V (x : Prop) : Prop := x = False ∨ p
#   have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
#   have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
#   let u : Prop := choose exU
#   let v : Prop := choose exV
#   have u_def : U u := choose_spec exU
#   have v_def : V v := choose_spec exV
  have not_uv_or_p : u ≠ v ∨ p :=
    match u_def, v_def with
    | Or.inr h, _ => Or.inr h
    | _, Or.inr h => Or.inr h
    | Or.inl hut, Or.inl hvf =>
      have hne : u ≠ v := by simp [hvf, hut, true_ne_false]
      Or.inl hne
#   sorry
# end Hidden
```

一方、``p`` が真であれば、関数外延性と命題外延性によって ``U`` と ``V`` は等しい。``u`` と ``v`` の定義により、``u`` と ``v`` も等しいことがわかる。 

```lean
# namespace Hidden
# open Classical
# theorem em (p : Prop) : p ∨ ¬p :=
#   let U (x : Prop) : Prop := x = True ∨ p
#   let V (x : Prop) : Prop := x = False ∨ p
#   have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
#   have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
#   let u : Prop := choose exU
#   let v : Prop := choose exV
#   have u_def : U u := choose_spec exU
#   have v_def : V v := choose_spec exV
#   have not_uv_or_p : u ≠ v ∨ p :=
#     match u_def, v_def with
#     | Or.inr h, _ => Or.inr h
#     | _, Or.inr h => Or.inr h
#     | Or.inl hut, Or.inl hvf =>
#       have hne : u ≠ v := by simp [hvf, hut, true_ne_false]
#       Or.inl hne
  have p_implies_uv : p → u = v :=
    fun hp =>
    have hpred : U = V :=
      funext fun x =>
        have hl : (x = True ∨ p) → (x = False ∨ p) :=
          fun _ => Or.inr hp
        have hr : (x = False ∨ p) → (x = True ∨ p) :=
          fun _ => Or.inr hp
        show (x = True ∨ p) = (x = False ∨ p) from
          propext (Iff.intro hl hr)
    have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV := by
      rw [hpred]; intros; rfl
    show u = v from h₀ _ _
#   sorry
# end Hidden
```

``not_uv_or_p`` と ``p_implies_uv`` をまとめると、所望の結論が得られる:

```lean
# namespace Hidden
# open Classical
# theorem em (p : Prop) : p ∨ ¬p :=
#   let U (x : Prop) : Prop := x = True ∨ p
#   let V (x : Prop) : Prop := x = False ∨ p
#   have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
#   have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
#   let u : Prop := choose exU
#   let v : Prop := choose exV
#   have u_def : U u := choose_spec exU
#   have v_def : V v := choose_spec exV
#   have not_uv_or_p : u ≠ v ∨ p :=
#     match u_def, v_def with
#     | Or.inr h, _ => Or.inr h
#     | _, Or.inr h => Or.inr h
#     | Or.inl hut, Or.inl hvf =>
#       have hne : u ≠ v := by simp [hvf, hut, true_ne_false]
#       Or.inl hne
#   have p_implies_uv : p → u = v :=
#     fun hp =>
#     have hpred : U = V :=
#       funext fun x =>
#         have hl : (x = True ∨ p) → (x = False ∨ p) :=
#           fun _ => Or.inr hp
#         have hr : (x = False ∨ p) → (x = True ∨ p) :=
#           fun _ => Or.inr hp
#         show (x = True ∨ p) = (x = False ∨ p) from
#           propext (Iff.intro hl hr)
#     have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV := by
#       rw [hpred]; intros; rfl
#     show u = v from h₀ _ _
  match not_uv_or_p with
  | Or.inl hne => Or.inr (mt p_implies_uv hne)
  | Or.inr h   => Or.inl h
# end Hidden
```

排中律の系としては、二重否定除去、場合分けによる証明、矛盾による証明などがあり、これらは全て節[Classical Logic (古典論理)](./propositions_and_proofs.md#classical-logic-古典論理)で説明されている。排中律と命題外延性は命題完全性を含意する:

```lean
# namespace Hidden
open Classical
theorem propComplete (a : Prop) : a = True ∨ a = False :=
  match em a with
  | Or.inl ha => Or.inl (propext (Iff.intro (fun _ => ⟨⟩) (fun _ => ha)))
  | Or.inr hn => Or.inr (propext (Iff.intro (fun h => hn h) (fun h => False.elim h)))
# end Hidden
```

選択原理と合わせると、「全ての命題は決定可能である」というより強い原理も得られる。決定可能命題のクラス ``Decidable`` は次のように定義されることを思い出してほしい:

```lean
# namespace Hidden
class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)  : Decidable p
# end Hidden
```

除去により ``Prop`` 型の項しか作れない ``p ∨ ¬ p`` とは対照的に、型 ``Decidable p`` は直和型 ``Sum p (¬ p)`` と等価であり、除去により任意の型の項を作ることができる。型 ``Decidable p`` のデータはif-then-else式を書くのに必要である。

古典的推論の例と同様に、「``f : α → β`` が単射で ``α`` が有項なら、``f`` は左逆写像を持つ」という定理を証明するためにも ``choose`` を使う。左逆写像 ``linv`` を定義するために、依存if-then-else式を用いる。``if h : c then t else e`` は ``dite c (fun h : c => t) (fun h : ¬ c => e)`` の略記であることを思い出してほしい。``linv`` の定義の中で、選択原理は2回使われている: 選択原理は、まず ``(∃ a : A, f a = b)`` が「決定可能」であることを示すために、そして ``f a = b`` を満たす ``a`` を選ぶために使われている。``propDecidable`` はスコープ付きインスタンスであり、``open Classical`` コマンドによって利用可能になることに注意してほしい。このインスタンスにより、このif-then-else式の使用が正当化される(節[Decidable Propositions (決定可能命題)](./type_classes.md#decidable-propositions-決定可能命題)の説明も参照のこと)。

```lean
open Classical

noncomputable def linv [Inhabited α] (f : α → β) : β → α :=
  fun b : β => if ex : (∃ a : α, f a = b) then choose ex else default

theorem linv_comp_self {f : α → β} [Inhabited α]
                       (inj : ∀ {a b}, f a = f b → a = b)
                       : linv f ∘ f = id :=
  funext fun a =>
    have ex  : ∃ a₁ : α, f a₁ = f a := ⟨a, rfl⟩
    have feq : f (choose ex) = f a  := choose_spec ex
    calc linv f (f a)
      _ = choose ex := dif_pos ex
      _ = a         := inj feq
```

古典的な観点からすると、``linv`` は関数である。構成的な観点からすると、``linv`` の定義は受け入れがたい: 一般にこのような関数を実装する方法はないため、この構築は何の情報も持たない。
