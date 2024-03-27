# Tactics (タクティク)

この章では、*tactics*(タクティク)を使って証明を構築する方法について説明する。証明項とは数学的証明の表現であり、タクティクは数学的証明を構築する手順を記述するコマンド(指示)である。定理 A ↔ B を証明する際に、非形式的に、「まず A → B を証明する。最初に定義を展開し、次に既存の補題を適用し、それから式を単純化する」という導入から数学の証明を始めることがあるかもしれない。これらの言明が証明を見つける方法を読者に伝える指示であるのと同様に、タクティクは証明項を構築する方法をLeanに伝える指示である。タクティクは、証明を分解し、一歩ずつゴールに向かうという段階的な証明の書き方を自然にサポートする。

タクティクの連続からなる証明を「タクティクスタイル」の証明と呼び、これまで見てきた証明項の構築の仕方を「項スタイル」の証明と呼ぶ。それぞれのスタイルには長所と短所がある。例えば、タクティクスタイルの証明は、各タクティクの結果を予測・推測することを読者に要求するため、項スタイルの証明より読みにくいという短所がある。しかし、短くて書きやすいという長所もある。さらに、タクティクはLeanの自動証明を利用するための入り口になる。なぜなら、Leanに自動証明を指示するコマンド自体がタクティクだからである。

## 用語に関する注意

この節は翻訳に際して追加した節である。

この章では、含意命題 ``p → q`` あるいはより一般的に依存関数型 ``(x : α) → β`` の中に登場する型 ``p`` や型 ``(x : α)`` を「前件(antecedent)」、型 ``q`` や型 ``β`` を「後件(consequent)」と呼び、一方で「ゴール(Goal)」 ``A ⊢ B`` の中に登場する項の集まり A を「コンテキスト(Context)」または「前提(Premise)」、ゴールにおいて項構築の目標となる型 B を「ターゲット(Target)」または「結論(Conclusion)」と呼び明確に区別する。特に、ゴールが閉じられていない(open)／未達成(not accomplished)／未証明(not proved)／未解決(not solved)のときは「コンテキスト(Context)」「ターゲット(Target)」という用語を使い、ゴールが閉じられている(closed)／達成済み(accomplished)／証明済み(proved)／解決済(solved)のときは「前提(Premise)」「結論(Conclusion)」という用語を使う。

コンテキスト(あるいは前提)に含まれる各項を「仮説(Hypothesis)」と呼ぶ。

ここでいう「ターゲット」を「ゴール」と呼ぶこともあるが、混乱を避けるため本訳ではこのような用語の使い方はしない。

``intro`` タクティクや ``revert`` タクティクの働きを理解する際に、この用語の区別が重要となる。

### 参考記事

- [コンテキストと組織化原理 - (新) 檜山正幸のキマイラ飼育記 メモ編](https://m-hiyama-memo.hatenablog.com/entry/2023/01/30/130823)
- [証明とリーズニング - (新) 檜山正幸のキマイラ飼育記 メモ編](https://m-hiyama-memo.hatenablog.com/entry/2023/01/22/130943)


## Entering Tactic Mode (タクティクモードへの入り方)

定理を述べたり、have文を使うと、ゴール、すなわち期待された型を持つ項を構築するという目標が生成される。例えば、仮説 ``p q : Prop``、``hp : p``、``hq : q`` を持つコンテキストでは、次のような記述は ``p ∧ q ∧ p`` という型の項を構築するというゴールを作成する:

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  sorry
```

このゴールは次のように記述できる:

```
    p : Prop, q : Prop, hp : p, hq : q ⊢ p ∧ q ∧ p
```

実際、上記の例で "sorry" をアンダースコアに置き換えると、Leanはまさにこのゴールが未解決であることを報告する。

通常は、明示的に証明項を記述することでこのようなゴールを達成する。しかし、Leanでは、項が記述されることが期待される任意の場所に、項の記述の代わりに ``by <tactics>`` ブロックを挿入することができる。ここで、``<tactics>`` はセミコロンまたは改行で区切られたコマンドの列である。``by <tactics>`` ブロックを使って上記の定理を証明することができる:

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  by apply And.intro
     exact hp
     apply And.intro
     exact hq
     exact hp
```

つまり、``by`` キーワードを書くことでタクティクモードに入れるのである。しばしば ``by`` キーワードは前の行に書き、上記の例はこのように書かれる:

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp
```

``apply`` タクティクは、0個以上の引数をとる関数を表現する項 ``t`` を現在のゴールに適用する。``apply`` タクティクは現在のゴールのターゲット(``⊢`` の後に書かれる型)と関数 ``t`` の出力の型を同一視し、引数(関数 ``t`` の入力の型を持つ項)を構築するという新しいゴールを作る。ただし、後続の引数の型が先行の引数に依存しない場合に限る。上記の例では、コマンド ``apply And.intro`` は2つのサブゴールを生成する:

```
    case left
    p q : Prop
    hp : p
    hq : q
    ⊢ p

    case right
    p q : Prop
    hp : p
    hq : q
    ⊢ q ∧ p
```

最初のゴールはコマンド ``exact hp`` で達成される。``exact`` コマンドは ``apply`` コマンドの一種で、「与えられた項がターゲットと同じ型を持つことを確認し、確認できたらゴールを閉じよ」とLeanに指示する。``exact`` コマンドをタクティク証明で使うのは良いことである。なぜなら、``exact`` コマンドの失敗は何かが間違っていることを示すからである。また ``exact`` は ``apply`` よりもロバストである。なぜなら、elaboratorは、与えられた項を処理する際に、今期待されている型(ゴールのターゲット)が何であるかを考慮に入れるからである。しかしながら、上記の例では ``apply`` も同様に機能する。

``#print`` コマンドを使って最終的に得られた証明項を確認することができる:

```lean
# theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
#  apply And.intro
#  exact hp
#  apply And.intro
#  exact hq
#  exact hp
#print test
/-
theorem test : ∀ (p q : Prop), p → q → p ∧ q ∧ p :=
fun p q hp hq => { left := hp, right := { left := hq, right := hp } }
-/
```

タクティク証明は段階的に書くことができる。VS Codeでは、``Ctrl-Shift-Enter`` を押すことでメッセージウィンドウを開くことができる。カーソルがタクティクブロック内にあるときはいつでも、このウィンドウは現在のゴールを表示する。Emacsでは、タクティクブロック内の任意の行末で ``C-c C-g`` を押すことで現在のゴールを見ることができる。また、カーソルを最後のタクティクの1文字目に置くことで、不完全な証明内の残りのゴールを見ることができる。証明が不完全な場合、キーワード ``by`` に赤い波線が引かれ、エラーメッセージには残りのゴールが表示される。

タクティクコマンドは単一の項名だけでなく、複合式を受け取ることもできる。以下は、前述の証明の短縮版である:

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  exact And.intro hq hp
```

当然のことながら、この証明記述は全く同じ証明項を生成する。

```lean
# theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
#  apply And.intro hp
#  exact And.intro hq hp
#print test
```

複数のタクティク適用をセミコロンで連結して1行で書くことができる。

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp
```

複数のサブゴールを生成する可能性のあるタクティクは、自動的に各サブゴールにタグを付けることが多い。例えば、タクティク ``apply And.intro`` は最初のサブゴールにタグ ``left`` を、2つ目のサブゴールにタグ ``right`` を付ける。この場合において、タグ名は ``And.intro`` の宣言の中で使われた引数の名前から推測される。``case <tag> => <tactics>`` という表記を使うことで、タクティクを構造化することができる。つまり、``<tactics>`` をどのタグ付けされたサブゴールに適用するかを明示することができる。以下は、この章の最初のタクティク証明の構造化されたバージョンである:

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
```

``case`` 記法を使うと、サブゴール ``right`` を ``left`` よりも先に解くことができる:

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
  case left => exact hp
```

``case`` ブロック内で、Leanが他のゴールを隠していることに注意してほしい。言わば、Leanは選択されたゴールに「集中」しているのである。さらに、``case`` ブロックの終了時に選択されたゴールが完全には解かれていない場合、Leanはエラーフラグを建てる。

サブゴールが単純である場合、タグを使ってサブゴールを選択する価値はないかもしれないが、その場合でも証明を構造化したい場合は ``case`` が有用である。また、Leanは証明を構造化するための「箇条書き」記法 ``. <tactics>`` (あるいは ``· <tactics>``) を提供する。``. <tactics>`` 記法を使うと、Leanは一番上のゴールに「集中」する。

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp
```

## Basic Tactics (基本的なタクティク)

``apply`` と ``exact`` に加えて、もう一つの便利なタクティクが ``intro`` である。``intro`` タクティクはゴールのターゲットの前件(ゴールのターゲットの ``→`` の前にある命題)をゴールのコンテキスト(ゴールの ``⊢`` の前)に移動させる。以降、この ``intro`` タクティクの機能を「ターゲットの前件をコンテキストに導入する」または単に「導入する」と表現する。以下は、3章で証明した命題論理の恒真式を今一度タクティクを使って証明した例である。

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim (And.right h)
    . intro hq
      apply Or.inl
      apply And.intro
      . exact And.left h
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact And.left h
      . exact hr
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      . exact And.left hpq
      . apply Or.inl
        exact And.right hpq
    . intro hpr
      apply And.intro
      . exact And.left hpr
      . apply Or.inr
        exact And.right hpr
```

``intro`` タクティクはより一般的に任意の型の項をコンテキストに導入できる:

```lean
example (α : Type) : α → α := by
  intro a
  exact a

example (α : Type) : ∀ x : α, x = x := by
  intro x
  exact Eq.refl x
```

``intro`` タクティクは複数の項を一度に導入できる:

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂
  exact Eq.trans (Eq.symm h₂) h₁
```

``apply`` タクティクが対話的に関数適用を構築するためのコマンドであるように、``intro`` タクティクは対話的に関数抽象(つまり ``fun x => e`` の形の項)を構築するためのコマンドである。ラムダ抽象記法と同様に、``intro`` タクティクでは暗黙の ``match`` を使うことができる。

```lean
example (α : Type) (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩
```

また、``intro`` タクティクは ``match`` 式のようにコンテキストに導入した項を場合分けすることもできる(詳しくは[8章 Induction and Recursion (帰納と再帰)](./induction_and_recursion.md)を参照のこと)。

```lean
example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
  | ⟨w, Or.inl h⟩ => exact ⟨w, Or.inr h⟩
  | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩

example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro h
  let ⟨w, hpq⟩ := h
  exact Or.elim hpq (fun hp : p w => ⟨w, Or.inr hp⟩) (fun hq : q w => ⟨w, Or.inl hq⟩)
```

``intros`` タクティクは引数を与えずに使うことができる。その場合、``intros`` タクティクはできる限り多くの項を一度に導入し、導入した各項に自動で名前を付ける。その例はすぐ後に紹介する。

``assumption`` タクティクは現在のゴールの仮説たちに目を通し、それらの中にゴールのターゲットと合致するものがあればそれを適用する。

```lean
example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  assumption   -- applied h₃
```

``assumption`` タクティクは、必要に応じてゴールのターゲット内のメタ変数( ``?b`` など、どんな項が代入されるかが未決定の変数)を解決する(メタ変数に具体的な項を代入する):

```lean
example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans
  assumption      -- solves x = ?b with h₁
  apply Eq.trans
  assumption      -- solves y = ?h₂.b with h₂
  assumption      -- solves z = w with h₃
```

次の例では、``intros`` タクティクを用いて3つの変数と2つの命題の証明を自動的にコンテキストに導入している:

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption
```

デフォルトでは、Leanが自動生成した名前( ``a✝`` など)にはアクセスできないことに注意してほしい。この仕様はタクティク証明の成否が自動生成された名前に依存しないようにするためにあり、この仕様があるおかげで証明はよりロバストになる。ただし、キーワード ``unhygienic`` を ``by`` の後に書くことでこの制限を無効にすることができる(証明のロバスト性は低下する)。

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by unhygienic
  intros
  apply Eq.trans
  apply Eq.symm
  exact a_2
  exact a_1
```

また、``rename_i`` タクティクを用いて、現在のゴール内の最も直近のアクセス不能な名前を変更することができる。次の例では、タクティク ``rename_i h1 _ h2`` がゴール内の最後の3つの仮説のうち2つの名前を変更している。

```lean
example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intros
  rename_i h1 _ h2
  apply Eq.trans
  apply Eq.symm
  exact h2
  exact h1
```

``rfl`` タクティクは ``exact rfl`` の、つまり ``exact Eq.refl _`` の糖衣構文である。

```lean
example (y : Nat) : (fun x : Nat => 0) y = 0 := by
  rfl

example (y : Nat) : (fun x : Nat => 0) y = 0 := by
  exact Eq.refl _
```

タクティクの前に ``repeat`` キーワードを書くと、そのタクティクは何度か繰り返し適用される。

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption
```

``revert`` タクティクは時々有用である。これは ``intro`` タクティクの逆の機能を持つ。つまり、指定した項をゴールのコンテキストからゴールのターゲットの前件に移動させる。以降、``revert`` タクティクの機能を「コンテキストの一部をターゲットに戻す」または単に「戻す」と表現する。

```lean
example (x : Nat) : x = x := by
  revert x
  -- goal is ⊢ ∀ (x : Nat), x = x
  intro y
  -- goal is y : Nat ⊢ y = y
  rfl
```

(この章の最初に書いたように用語の区別をしていれば明らかなことだが、)コンテキスト(の一部)をターゲットに移すと含意命題が得られる:

```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert h
  -- goal is x y : Nat ⊢ x = y → y = x
  intro h₁
  -- goal is x y : Nat, h₁ : x = y ⊢ y = x
  apply Eq.symm
  assumption
```

しかし、``revert`` はさらに賢く、指定した項だけでなく、指定した項に依存する型を持つ要素も全てゴールのターゲットに移動させる。例えば、上の例で ``x`` を戻すと、``h`` も一緒に戻される:

```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert x
  -- goal is y : Nat ⊢ ∀ (x : Nat), x = y → y = x
  intros
  apply Eq.symm
  assumption
```

また、コンテキスト内の複数の仮説を一度に戻すこともできる:

```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert x y
  -- goal is ⊢ ∀ (x y : Nat), x = y → y = x
  intros
  apply Eq.symm
  assumption
```

``revert`` で戻せるのは現在のゴールのコンテキスト内の項(仮説)だけである。しかし、タクティク ``generalize e = x`` を使えば、ゴールのターゲットに登場する任意の式 ``e`` を新しい変数 ``x`` に置き換えることができる。また、タクティク ``generalize e = x at h₁`` を使えば、ゴールの仮説 ``h₁`` に登場する任意の式 ``e`` を新しい変数 ``x`` に置き換えることができる。

```lean
example : 3 = 3 := by
  generalize 3 = x
  -- goal is x : Nat ⊢ x = x
  revert x
  -- goal is ⊢ ∀ (x : Nat), x = x
  intro y
  -- goal is y : Nat ⊢ y = y
  rfl
```

上記の例において、``generalize 3 = x`` は ``3`` に任意の変数 ``x`` を割り当てることでゴールのターゲットを一般化している。全ての一般化がゴールの証明可能性を保存するわけではないことに注意してほしい。次の例では、``generalize`` が ``rfl`` を使うだけで証明できるゴールを決して証明できないゴールに置き換えている:

```lean
example : 2 + 3 = 5 := by
  generalize 3 = x
  -- goal is x : Nat ⊢ 2 + x = 5
  admit
```

``admit`` タクティクは ``exact sorry`` の糖衣構文である。これは現在のゴールを閉じ、``sorry`` が使われたという警告を出す。一般化以前のゴールの証明可能性を保存するために、``generalize`` タクティクを使う際に ``3`` が ``x`` に置き換えられたという事実を記録することができる。そのためには、置き換えの事実を保存するためのラベルを ``generalize`` に与えるだけでよい:

```lean
example : 2 + 3 = 5 := by
  generalize h : 3 = x
  -- goal is x : Nat, h : 3 = x ⊢ 2 + x = 5
  rw [← h]
```

ここでは、``rewrite`` タクティク(略称は ``rw``)が ``h`` を用いて ``x`` を ``3`` で再び置き換えている。``rewrite`` タクティクについては後述する。

## More Tactics (他のタクティク)

命題やデータを構築したり分解したりするには、他のいくつかのタクティクが有用である。例えば、``p ∨ q`` の形のターゲットに対して ``apply`` タクティクを使う場合は、タクティク ``apply Or.inl`` や ``apply Or.inr`` を使うだろう。逆に、``cases`` タクティクは選言命題型(など)の仮説を分解する。

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq
```

``cases`` タクティクの構文は ``match`` 式の構文と似ていることに注意。新しいサブゴールは好きな順番で解くことができる。

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inr hq => apply Or.inl; exact hq
  | inl hp => apply Or.inr; exact hp
```

``with`` と後続のタクティクを書かずに(構造化されていない) ``cases`` を使うこともできる。この場合、複数のサブゴールが生成される。

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption
```

(構造化されていない) ``cases`` は、同じタクティクを使って複数のサブゴールを閉じられる場合に特に便利である。

```lean
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  repeat assumption
```

``tac1 <;> tac2`` という結合子を使えば、タクティク ``tac1`` により生成された各サブゴールに ``tac2`` を適用することもできる。

```lean
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption
```

構造化されていない ``cases`` タクティクと ``case`` 記法や ``.`` 記法を組み合わせることができる。

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  . apply Or.inr
    assumption
  . apply Or.inl
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  case inl h =>
    apply Or.inr
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  . apply Or.inr
    assumption
```

``cases`` タクティクは連言命題を分解することもできる。

```lean
example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq => constructor; exact hq; exact hp

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq => apply And.intro; exact hq; exact hp
```

この例では、``cases`` タクティクにより ``h : p ∧ q`` が一対の項 ``hp : p`` と ``hq : q`` に置き換えられた。``constructor`` タクティクは、連言のための唯一のコンストラクタ ``And.intro`` をターゲットに適用する。これらのタクティクにより、前節の例は以下のように書き換えられる:

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro hp hqr =>
      cases hqr
      . apply Or.inl; constructor <;> assumption
      . apply Or.inr; constructor <;> assumption
  . intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | intro hp hq => constructor; exact hp; apply Or.inl; exact hq
    | inr hpr =>
      cases hpr with
      | intro hp hr => constructor; exact hp; apply Or.inr; exact hr
```

これらのタクティクを非常に一般的に用いることができることは、[7章 Inductive Types (帰納型)](./inductive_types.md)で説明する。端的に説明すると、``cases`` タクティクは帰納的に定義された型の任意の項を分解することができる。``constructor`` タクティクは常に、帰納的に定義された型の適用可能な最初のコンストラクタを適用する。例えば、``cases`` と ``constructor`` は存在量化子に対して使うことができる:

```lean
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => constructor; apply Or.inl; exact px

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => apply Exists.intro; apply Or.inl; exact px
```

ここでは、``constructor`` タクティクは ``Exists.intro`` の最初の引数である ``x`` の値を暗黙のままにしている。これは一旦メタ変数で表され、後でインスタンス化される。前の例では、メタ変数の適切な値はタクティク ``exact px`` が使われた時点で決定される。なぜなら、``px`` は型 ``p x`` を持つからである。存在量化子に対する証人を明示的に指定したい場合は、代わりに ``exists`` タクティクを使うことができる:

```lean
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => exists x; apply Or.inl; exact px
```

これは他の例である:

```lean
example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  cases h with
  | intro x hpq =>
    cases hpq with
    | intro hp hq =>
      exists x
```

``cases`` タクティクや``constructor`` タクティクは命題だけでなくデータにも使える。次の例では、直積型の項の成分を入れ替える関数と直和型の項の成分を入れ替える関数を定義するためにこれらのタクティクが使われている:

```lean
def swap_pair : α × β → β × α := by
  intro p
  cases p
  constructor <;> assumption

def swap_sum : Sum α β → Sum β α := by
  intro p
  cases p
  . apply Sum.inr; assumption
  . apply Sum.inl; assumption

theorem swap_and : a ∧ b → b ∧ a := by
  intro p
  cases p
  constructor <;> assumption

theorem swap_or : a ∨ b → b ∨ a := by
  intro p
  cases p
  . apply Or.inr; assumption
  . apply Or.inl; assumption
```

上2つの関数定義の記述と、下2つの定理の証明が、わずかな差を除いて同じであることに注意してほしい。

``cases`` タクティクは自然数を「場合分け」することもできる:

```lean
open Nat
example (P : Nat → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : Nat) : P m := by
  cases m with
  | zero    => exact h₀
  | succ m' => exact h₁ m'
```

``cases`` タクティクとその仲間である ``induction`` タクティクについては、[Tactics for Inductive Types (帰納型のためのタクティク)](./inductive_types.md#tactics-for-inductive-types-帰納型のためのタクティク)節で詳しく説明する。

``contradiction`` タクティクは現在のゴールのコンテキストの中から矛盾を探す:

```lean
example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction
```

``match`` はタクティクブロック内でも使うことができる。

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    match h with
    | ⟨_, Or.inl _⟩ => apply Or.inl; constructor <;> assumption
    | ⟨_, Or.inr _⟩ => apply Or.inr; constructor <;> assumption
  . intro h
    match h with
    | Or.inl ⟨hp, hq⟩ => constructor; exact hp; apply Or.inl; exact hq
    | Or.inr ⟨hp, hr⟩ => constructor; exact hp; apply Or.inr; exact hr
```

``intro h`` を ``match h ...`` と「組み合わせる」と、上記の例は次のように書ける:

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro
    | ⟨hp, Or.inl hq⟩ => apply Or.inl; constructor <;> assumption
    | ⟨hp, Or.inr hr⟩ => apply Or.inr; constructor <;> assumption
  . intro
    | Or.inl ⟨hp, hq⟩ => constructor; assumption; apply Or.inl; assumption
    | Or.inr ⟨hp, hr⟩ => constructor; assumption; apply Or.inr; assumption
```

## Structuring Tactic Proofs (タクティク証明の構造化)

タクティクはしばしば証明を構築する効率的な方法を提供するが、長いタクティクの列は証明の構造を不明瞭にすることがある。このセクションでは、タクティクスタイルの証明をより読みやすくよりロバストにするために、タクティクスタイルの証明を構造化する方法を説明する。

Leanの証明記述構文の優れている点のひとつは、項スタイルの証明とタクティクスタイルの証明をミックスさせて、その間を自由に行き来できることだ。例えば、``apply`` タクティクや ``exact`` タクティクは ``have`` や ``show`` などを使って書かれた任意の型の項を受け取ることができる。逆に、Leanで任意の項を書くときは、``by`` キーワードを挿入することで、いつでもタクティクモードを呼び出すことができる。以下はその例である:

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  exact
    have hp : p := h.left
    have hqr : q ∨ r := h.right
    show (p ∧ q) ∨ (p ∧ r) by
      cases hqr with
      | inl hq => exact Or.inl ⟨hp, hq⟩
      | inr hr => exact Or.inr ⟨hp, hr⟩
```

次はより自然な例である:

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq => exact Or.inl ⟨h.left, hq⟩
    | inr hr => exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq => exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr => exact ⟨hpr.left, Or.inr hpr.right⟩
```

実際、``show`` タクティクというものがあり、これは項スタイルの証明の ``show`` 式に似ている。これは、タクティクモードの中で、解こうとしているゴールのターゲットの型を宣言するだけのタクティクである。

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inl ⟨h.left, hq⟩
    | inr hr =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq =>
      show p ∧ (q ∨ r)
      exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr =>
      show p ∧ (q ∨ r)
      exact ⟨hpr.left, Or.inr hpr.right⟩
```

実は、``show`` タクティクは、ゴールのターゲットをdefinitionally equalな他の表現に書き換えるために使うことができる:

```lean
example (n : Nat) : n + 1 = Nat.succ n := by
  -- goal is n: Nat ⊢ n + 1 = Nat.succ n
  show Nat.succ n = Nat.succ n
  -- goal is n: Nat ⊢ Nat.succ n = Nat.succ n
  rfl

example (n : Nat) : n + 1 = Nat.succ n := by
  -- goal is n: Nat ⊢ n + 1 = Nat.succ n
  rfl
```

項スタイルの証明のときと同様に、``have`` タクティクは、宣言した型の項を作るというサブゴールを導入する:

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have hpq : p ∧ q := And.intro hp hq
    apply Or.inl
    exact hpq
  | inr hr =>
    have hpr : p ∧ r := And.intro hp hr
    apply Or.inr
    exact hpr
```

項スタイルの証明のときと同様に、``have`` タクティクでは項に付けるラベルを省略することもできる。その場合、デフォルトのラベル ``this`` が使われる:

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have : p ∧ q := And.intro hp hq
    apply Or.inl
    exact this
  | inr hr =>
    have : p ∧ r := And.intro hp hr
    apply Or.inr
    exact this
```

``have`` タクティクでは型も省略することができる。したがって、``have hp := h.left`` や ``have hqr := h.right`` と書くことができる。これらの省略記法を用いると、``have`` タクティクにおいて型とラベルの両方を省略することさえできる。その場合、新しい項にはデフォルトのラベル ``this`` が使われる。

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  cases hqr with
  | inl hq =>
    have := And.intro hp hq
    apply Or.inl; exact this
  | inr hr =>
    have := And.intro hp hr
    apply Or.inr; exact this
```

Leanには ``let`` タクティクもある。これは ``have`` タクティクに似ているが、``have`` タクティクが補助的な事実を導入するのに対して、``let`` タクティクは局所的な定義を導入する。これは項スタイルの証明における ``let`` に類似したタクティクである。

```lean
example : ∃ x, x + 2 = 8 := by
  let a : Nat := 3 * 2
  exists a
```

``have`` と同様に、``let a := 3 * 2`` と書くことで、型を暗黙のままにすることができる。``let`` と ``have`` の違いは、``let`` はコンテキストの中でローカルな定義を導入することである。ローカルに宣言された定義はその証明の中で展開することができる。

先ほど、``.`` を使って入れ子のタクティクブロックを作成した。入れ子のブロックの中では、Leanは最初のゴールに注目し、そのブロックの最後でそのゴールが完全に解決されていなければエラーを生成する。これは、タクティクによって導入された複数のサブゴールを一つ一つ証明するのに便利である。``.`` 記法はインデントに敏感である。なぜなら、インデントを見て各タクティクブロックが終了したかどうかを検知するからである。あるいは、波括弧とセミコロンを使ってタクティクブロックを表すこともできる。

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  { intro h;
    cases h.right;
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inl ⟨h.left, ‹q›⟩ }
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inr ⟨h.left, ‹r›⟩ } }
  { intro h;
    cases h;
    { show p ∧ (q ∨ r);
      rename_i hpq;
      exact ⟨hpq.left, Or.inl hpq.right⟩ }
    { show p ∧ (q ∨ r);
      rename_i hpr;
      exact ⟨hpr.left, Or.inr hpr.right⟩ } }
```

証明を構造化するためにインデントを使うと便利である: タクティクが2つ以上のサブゴールを残すたびに、残りのサブゴールをブロックで囲んでインデントして分離するとよい。もし定理 ``foo`` の適用が1つのゴールから4つのサブゴールを生成するなら、証明の見た目は次のようになるだろう:

```
  apply foo
  . <proof of first goal>
  . <proof of second goal>
  . <proof of third goal>
  . <proof of final goal>
```

あるいは

```
  apply foo
  case <tag of first goal>  => <proof of first goal>
  case <tag of second goal> => <proof of second goal>
  case <tag of third goal>  => <proof of third goal>
  case <tag of final goal>  => <proof of final goal>
```

あるいは

```
  apply foo
  { <proof of first goal>  }
  { <proof of second goal> }
  { <proof of third goal>  }
  { <proof of final goal>  }
```

## Tactic Combinators (タクティク結合子)

*Tactic combinators*(タクティク結合子) は既存のタクティクから新しいタクティクを作る。逐次結合子 ``;`` は ``by`` ブロックの中で既に暗黙のうちに使われている:

```lean
example (p q : Prop) (hp : p) : p ∨ q :=
  by apply Or.inl; assumption
```

ここで、``apply Or.inl; assumption`` はまず単一のタクティク ``apply Or.inl`` を使ってから ``assumption`` を使うのと機能的に同等である。

``t₁ <;> t₂`` において、結合子 ``<;>`` は逐次結合子の「パラレル」版である: まず ``t₁`` が現在のゴールに適用される。それから ``t₂`` がサブゴール「全て」に適用される。

```lean
example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  by constructor <;> assumption
```

この方法は、``t₁`` の適用の結果得られるサブゴールが一様の形式を持つ場合、あるいは少なくとも、全てのゴールを一様な方法で進めることができる場合に特に有効である。

``first | t₁ | t₂ | ... | tₙ`` はどれか一つが成功するまで各 ``tᵢ`` を適用する。その全てが成功しなかったら失敗する:

```lean
example (p q : Prop) (hp : p) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption

example (p q : Prop) (hq : q) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption
```

最初の例では左のタクティクが成功し、2番目の例では右のタクティクが成功している。次の3つの例では、いずれも同じ複合タクティクにより証明が成功している。

```lean
example (p q r : Prop) (hp : p) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hq : q) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hr : r) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

/- repeat と first を使わなかった場合 -/

example (p q r : Prop) (hp : p) : p ∨ q ∨ r :=
  by apply Or.inl; assumption

example (p q r : Prop) (hq : q) : p ∨ q ∨ r :=
  by apply Or.inr
     apply Or.inl; assumption

example (p q r : Prop) (hr : r) : p ∨ q ∨ r :=
  by apply Or.inr
     apply Or.inr
     assumption
```

このタクティクはまず選言命題の左側をターゲットにし、それを ``assumption`` で解こうとする。それが失敗したら、選言命題の右側に注目する。もしそれも失敗したら、``assumption`` タクティクを呼び出す。

もう気付いているだろうが、タクティクは失敗することがある。実際、``first`` 結合子がバックトラックして次のタクティクを試すのは、一番最初のタクティクが「失敗」したときである。``try`` 結合子は、つまらないかもしれない方法によって、常に成功するタクティクを構築する: ``try t`` は ``t`` を実行し、たとえ ``t`` が失敗しても成功したと報告する。``try t`` は ``first | t | skip`` と等価である。ここで、``skip`` は何もせず、そして何もしないことで成功するタクティクである。次の例では、2番目の ``constructor`` は連言の右側 ``q ∧ r`` については成功するが、連言の左側 ``p`` については失敗する (連言と選言は右結合的であることを覚えておこう)。``try`` タクティクは逐次結合されたタクティクが成功することを保証する。

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption
```

**注意**: ``try t`` は決して失敗しないため、``repeat (try t)`` は無限にループする。

証明では、複数のゴールが未解決であることがよくある。並列逐次結合子 ``<;>`` は1つのタクティクを複数のゴールに適用する1つの方法だが、他にも方法はある。例えば、``all_goals t`` は全ての未解決のゴールに ``t`` を適用する:

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption
```

この例では、``any_goals`` タクティクはよりロバストな解を提供する。タクティク ``any_goals t``は ``all_goals t`` に似ているが、``any_goals t`` は ``t`` が少なくとも1つのゴールで成功すれば成功する。

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  any_goals constructor
  any_goals assumption
```

次の例において、最初のタクティクは連言命題を繰り返し分解する:

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)
  all_goals assumption
```

実際、上記の例の全てのタクティクを一行に詰め込むことができる:

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals (first | constructor | assumption))
```

タクティク ``focus t`` は、他のゴールを一時的にスコープから隠し、``t`` を現在のゴール(一番上のゴール)だけに作用させる。したがって、通常は ``t`` が現在のゴールだけに作用する場合、``focus (all_goals t)`` は ``all_goals`` の機能を打ち消して ``t`` と同じ作用を持つ。

## Rewriting (書き換え)

[Calculational Proofs (計算的証明)](./quantifiers_and_equality.md#calculational-proofs-計算的証明)の節で、``rewrite`` タクティク(省略版: ``rw``)と ``simp`` タクティクを簡単に紹介した。本節と次節では、これらについてさらに詳しく説明する。

``rewrite`` タクティクはターゲットとコンテキストに置換を適用するための基本的なメカニズムであり、等式を扱う便利で効率的な方法を提供する。このタクティクの最も基本的な構文は ``rewrite [t]`` である。ここで、``t`` はある等式が成立することを主張する型である。例えば、仮説 ``h : x = y`` を ``t`` として採用することができる。``t`` は ``add_comm : ∀ x y, x + y = y + x`` のような全称命題でもよい。その場合、``rewrite`` タクティクは ``x`` と ``y`` に対して適切なインスタンスを見つけようとする。あるいは、それが具体的な等式あるいは等式に関する全称命題であれば、``t`` は複合的な項であってもよい。次の例では、仮説を用いてターゲットを書き換えるために基本的な構文 ``rewrite [t]`` を使う。

```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂] -- replace k with 0
  rw [h₁] -- replace f 0 with 0
```

上記の例では、最初の ``rw`` はターゲット ``f k = 0`` 内の ``k`` を ``0`` に置き換え、2番目の ``rw`` はターゲット ``f 0 = 0`` 内の ``f 0`` を ``0`` に置き換えている。このタクティクは ``t = t`` という形の任意のゴールを(``rfl`` を使うまでもなく)自動的に閉じる。次は複合的な項を使った書き換えの例である:

```lean
example (x y : Nat) (p : Nat → Prop) (q : Prop) (h : q → x = y)
        (h' : p y) (hq : q) : p x := by
  rw [h hq]; assumption
```

ここで ``h hq`` は ``x = y`` の証明を構築している。

``rw [t_1, ..., t_n]`` という記法を使って、複数回の書き換えを1つにまとめることができる。これは ``rw [t_1]; ...; rw [t_n]`` の略記である。この記法を用いると、先ほどの例は次のように書ける:

```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂, h₁]
```

デフォルトでは、``rw`` は等式を順方向に用いる。つまり、書き換え対象の中で ``t`` の左辺とマッチした(全ての)部分項を ``t`` の右辺で置き換える。記法 ``←t`` を使うと、等式 ``t`` を逆向きに使うように指示することができる。つまり、書き換え対象の中で ``t`` の右辺とマッチした部分項を ``t`` の左辺で置き換えることができる。

```lean
example (f : Nat → Nat) (a b : Nat) (h₁ : a = b) (h₂ : f a = 0) : f b = 0 := by
  rw [←h₁, h₂]
```

この例では、項 ``←h₁`` は ``b`` を ``a`` に置き換えるよう書き換え器に指示する。エディターでは、``\l`` と打つと ``←`` を入力することができる。また、これと等価なアスキー文字列 ``<-`` を使うこともできる。

用いる等式が全称命題の場合、等式の左辺が書き換え対象内の複数の部分項とマッチすることがある。例えば、書き換え対象が ``a + b + c = a + c + b`` であるとき、``rw [Nat.add_comm]`` は ``a + b`` とも ``a + c`` とも ``a + b + c`` とも ``a + c + b`` ともマッチしうる。その場合、``rw`` タクティクは書き換え対象を走査したときに最初にマッチした部分項を書き換える。それが希望するものではない場合は、追加の引数を与えることでマッチさせたい部分項を指定することができる。

```lean
example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b, ← Nat.add_assoc]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm b]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm _ b]
```

上記の最初の例では、最初のステップで ``a + b + c`` を ``a + (b + c)`` に書き換えている。次のステップでは、項 ``b + c`` に可換性を適用している。ここで、引数 ``b`` を指定しなければ、``a + (b + c)`` が ``(b + c) + a`` に書き換えられていただろう。最後に、結合性を逆向きに使うことで ``a + (c + b)`` を ``a + c + b`` に書き換えている。次の2つの例では、まず結合性を2回使って両辺の括弧を右に寄せ、それから ``b`` と ``c`` を入れ替えている。最後の例では、``Nat.add_comm`` の第2引数を指定することで、左辺ではなく右辺の書き換えを指示していることに注意してほしい。

デフォルトでは、``rw`` タクティクはゴールのターゲットだけに影響する。``rw [t] at h`` という記法は、仮説 ``h`` に ``t`` による書き換えを適用する。

```lean
example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by
  rw [Nat.add_zero] at h
  rw [h]
```

最初のステップでは、``rw [Nat.add_zero] at h`` が仮説 ``h`` の型を ``a + 0 = 0`` から ``a = 0`` に書き換えている。それからターゲットを ``f 0 = f 0`` に書き換えるために ``h : a = 0`` が用いられている。

``rewrite`` タクティクは命題だけにとどまらず変数の型を書き換えることもできる。次の例では、``rw [h] at t`` が仮説 ``t : Tuple α n`` の型を ``t : Tuple α 0`` に書き換えている。

```lean
def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

example (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := by
  rw [h] at t
  exact t
```

## Using the Simplifier (単純化器の使用)

``rewrite`` タクティクがゴールを操作するために特化したツールとして設計されているのに対し、*simplifier*(単純化器) はより強力な自動化を提供する。Leanのライブラリには、``[simp]`` 属性が付けられた恒等式が多数収載されており、``simp`` タクティクはそれらを使って単純化対象内の部分項を繰り返し書き換える。

```lean
example (x y z : Nat) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp

example (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp; assumption
```

最初の例では、ターゲットの等式の左辺は、0と1を含む普通の恒等式を使って単純化され、ターゲットは ``x * y = x * y`` となる。この時点で、``simp`` は反射律を用いてゴールを閉じる。2番目の例では、``simp`` がゴールを ``p (x * y)`` に簡約し、その時点で ``h`` がゴールを閉じる。次はリストに関する例である:

```lean
open List

example (xs : List Nat)
        : reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs := by
  simp

example (xs ys : List α)
        : length (reverse (xs ++ ys)) = length xs + length ys := by
  simp [Nat.add_comm]
```

ここで、``simp [t]`` は ``[simp]`` 属性が付けられた恒等式に加えて ``t`` を用いて単純化対象を書き換える。

``rw`` と同様に、キーワード ``at`` を使うとコンテキスト内の仮説を単純化することができる:

```lean
example (x y z : Nat) (p : Nat → Prop)
        (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) := by
  simp at h; assumption
```

さらに、「ワイルドカード」``*`` を使うと、コンテキスト内の全ての仮説とターゲットを単純化することができる:

```lean
attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp at *; assumption

example (x y z : Nat) (p : Nat → Prop)
        (h₁ : p (1 * x + y)) (h₂ : p (x * z * 1))
        : p (y + 0 + x) ∧ p (z * x) := by
  simp at * <;> constructor <;> assumption
```

自然数の乗法のような可換性と結合性を満たす演算の場合、単純化器は可換性と結合性に加えて*left commutativity*(左結合性)を用いて式を書き換える。乗法の場合、左結合性は次のように表される: ``x * (y * z) = y * (x * z)``。``local`` 修飾子は、現在のファイル(あるいはセクションや名前空間)内でこれらの規則を使用するように単純化器に指示する。可換性と左可換性は、どちらか片方を繰り返し適用するとループが生じるという点で問題があるように思えるかもしれない。しかし、単純化器は引数を並べ替える恒等式を検出し、*ordered rewriting*(順序付き書き換え)として知られるテクニックを使用する。これは、システムが項の内部的な順序を保持し、項の順序が小さくなる場合にのみ恒等式を適用することを意味する。上記の可換性、結合性、左結合性の恒等式は全て、部分項中の括弧を右に寄せるという効果を持つ。そのため、項を(多少恣意的ではあるが)正規化された順序で並べることができる。したがって、結合性と可換性の下で等価な式は、同じ正規形に書き換えられる。

```lean
attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm
example (w x y z : Nat)
        : x * y + z * w * x = x * w * z + y * x := by
  simp

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp        -- ⊢ p (x * y + w * (x * z))
  simp at h   -- h: p (x * y + w * (x * z))
  assumption
```

``rewrite`` と同様に、``simp [t_1, ..., t_n]`` と書くことで、単純化の際に使用する恒等式のリストに ``t_1`` ... ``t_n`` を追加することができる。追加するものは一般的な補題でも仮説でも定義の展開でも複合的な項でもよい。``simp`` タクティクも ``rewrite`` と同様に ``←t`` 構文を認識する。

```lean
def f (m n : Nat) : Nat :=
  m + n + m

example {m n : Nat} (h : n = 1) (h' : 0 = m) : (f m n) = n := by
  simp [h, ←h', f]
```

仮説を用いてゴールを単純化するのがよくある使い方である:

```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [h₁, h₂]
```

単純化の際に全ての仮説を使いたい場合は、ワイルドカード記号 ``*`` を使う:

```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [*]
```

次は他の例である:

```lean
example (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x)
        : w = z + y + u := by
  simp [*, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
```

単純化器は命題の書き換えも行う。例えば、仮説 ``hp : p`` を用いて、``p ∧ q`` を ``q`` に、``p v q`` を ``True`` に書き換え、最終的に自明な命題に書き換えられたゴールを閉じる。命題の書き換えを繰り返すことで、非自明な命題推論を行うことができる。

```lean
example (p q : Prop) (hp : p) : p ∧ q ↔ q := by
  simp [*]

example (p q : Prop) (hp : p) : p ∨ q := by
  simp [*]

example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
  simp [*]
```

次の例では、単純化器はコンテキスト内の全ての仮説を単純化し、それらをターゲットに適用しゴールを閉じている。

```lean
example (u w x x' y y' z : Nat) (p : Nat → Prop)
        (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : x + y + 0 = x' + y' := by
  simp at *
  simp [*]
```

単純化器の特に便利なところは、ライブラリが発展するにつれてその機能が成長していくところだ。例えば、リスト ``xs`` を受け取ると、``xs`` に反転 ``xs.reverse`` を追加して ``xs`` を対称化するリスト演算 ``mk_symm`` を定義したとしよう:

```lean
def mk_symm (xs : List α) :=
  xs ++ xs.reverse
```

このとき、任意のリスト ``xs`` に対して、``List.reverse (mk_symm xs)`` が ``mk_symm xs`` と等しいことが、定義を展開することで容易に証明できる:

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]
```

``reverse_mk_symm`` が証明された今、新しい定理を証明するために ``reverse_mk_symm`` を使った単純化を用いることができる:

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
# theorem reverse_mk_symm (xs : List α)
#        : (mk_symm xs).reverse = mk_symm xs := by
#  simp [mk_symm]
example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp [reverse_mk_symm]

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp [reverse_mk_symm] at h; assumption
```

``simp [reverse_mk_symm]`` を使うのは一般的に決して悪いことではないが、ユーザーが明示的にこれを呼び出す必要がない方がなおよいだろう。定理を定義する際に、「これは単純化の際に使う定理だ」とマークすることで明示的な呼び出しの省略を実現できる:

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
@[simp] theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
```

記法 ``@[simp]`` は ``reverse_mk_symm`` が ``[simp]`` 属性を持つことを宣言する。この宣言はより明示的に記述することができる:

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

attribute [simp] reverse_mk_symm

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
```

定理が宣言された後なら、いつでもその定理に属性を付与することができる:

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp [reverse_mk_symm]

attribute [simp] reverse_mk_symm

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
```

しかし、一度属性が付与されると、それを永続的に削除する方法は**ない**。そして、属性は、その属性が割り当てられているファイルをインポートする全てのファイルに適用される。[Attributes (属性)](./interacting_with_lean.md#attributes-属性)の節で詳しく説明するが、``local`` 修飾子を使えば、属性の適用範囲を現在のファイルやセクションに限定することができる:

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

section
attribute [local simp] reverse_mk_symm

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
end
```

``local`` を使った場合、そのセクションの外では、単純化器はデフォルトで ``reverse_mk_symm`` を使わなくなる。

これまで説明してきた様々な ``simp`` のオプション (ルールの明示的なリストを与える、``at`` を使って適用対象を指定するなど) は組み合わせることができるが、オプションを記述する順序は厳格であることに注意してほしい。エディタの中では、``simp`` キーワードにカーソルを合わせて、``simp`` に関連するドキュメントを読むことで、オプションの正しい順序を確認することができる。

さらに2つの便利な修飾子がある。デフォルトでは、``simp`` は属性 ``[simp]`` でマークされた全ての定理を利用する。``simp only`` と書くと、デフォルトで使われる定理は全て除外され、より明確に作られた定理のリストを使うことができる。以下の例では、マイナス記号 ``-`` と ``only`` が ``reverse_mk_symm`` の適用をブロックするために使われている。

```lean
def mk_symm (xs : List α) :=
  xs ++ xs.reverse
@[simp] theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp [-reverse_mk_symm] at h; assumption

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp only [List.reverse_append] at h; assumption
```

``simp`` タクティクには多くの設定オプションがある。例えば、次のように文脈的な単純化(ターゲットの前件を用いた単純化)を有効にすることができる。

```lean
example : if x = 0 then y + x = y else x ≠ 0 := by
  simp (config := { contextual := true })
```

``contextual := true`` のとき、 ``simp`` は ``y + x = y`` を単純化する際は ``x = 0`` という事実を使い、``x ≠ 0`` を単純化する際には ``x ≠ 0`` を用いる。次は他の例である:

```lean
example : ∀ (x : Nat) (h : x = 0), y + x = y := by
  simp (config := { contextual := true })
```

もうひとつの便利な設定オプションは、算術的な単純化を可能にする ``arith := true`` である。これは非常に便利なので、``simp_arith`` は ``simp (config := { arith := true })`` の省略形になっている。

```lean
example : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
  simp_arith
```

## Split Tactic (Splitタクティク)

``split`` タクティクは、入れ子の ``if-then-else`` 式や ``match`` 式を場合分けするのに便利である。``n`` 個の場合分けを持つ ``match`` 式に対して、``split`` タクティクは最大 ``n`` 個のサブゴールを生成する。次に例を示す:

```lean
def f (x y z : Nat) : Nat :=
  match x, y, z with
  | 5, _, _ => y
  | _, 5, _ => y
  | _, _, 5 => y
  | _, _, _ => 1

example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f x y w = 1 := by
  intros
  simp [f]
  split
  . contradiction
  . contradiction
  . contradiction
  . rfl
```

上記の例のタクティク証明は次のように短縮することができる。

```lean
# def f (x y z : Nat) : Nat :=
#  match x, y, z with
#  | 5, _, _ => y
#  | _, 5, _ => y
#  | _, _, 5 => y
#  | _, _, _ => 1
example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f x y w = 1 := by
  intros; simp [f]; split <;> first | contradiction | rfl
```

タクティク ``split <;> first | contradiction | rfl`` は、まず ``split`` タクティクを適用し、次に生成された各サブゴールに対して ``contradiction`` を試し、それが失敗したら ``rfl`` を試す。``simp`` のように、``split`` をコンテキスト内の特定の仮説に適用することもできる。

```lean
def g (xs ys : List Nat) : Nat :=
  match xs, ys with
  | [a, b], _ => a+b+1
  | _, [b, c] => b+1
  | _, _      => 1

example (xs ys : List Nat) (h : g xs ys = 0) : False := by
  simp [g] at h; split at h <;> simp_arith at h
```

## Extensible Tactics (拡張可能なタクティク)

次の例では、コマンド ``syntax`` を使って ``triv`` という記法を定義する。次に、``macro_rules`` コマンドを使って、``triv`` が使われたときの処理を指定する(``triv`` のマクロ展開を指定する)。``triv`` に対して複数のマクロ展開を指定することができ、タクティク解釈器はどれかが成功するまで全てのマクロ展開を試す。

```lean
-- 新しい記法を定義する
syntax "triv" : tactic

macro_rules
  | `(tactic| triv) => `(tactic| assumption)

example (h : p) : p := by
  triv

-- 現時点では、`triv` を使って次の定理を証明することはできない
-- example (x : α) : x = x := by
--  triv

-- `triv` を拡張しよう。タクティク解釈器はどれかが成功するまで
-- `triv` のための全てのマクロ展開を試す
macro_rules
  | `(tactic| triv) => `(tactic| rfl)

example (x : α) : x = x := by
  triv

example (x : α) (h : p) : x = x ∧ p := by
  apply And.intro <;> triv

-- (再帰的な)マクロ展開を追加する
macro_rules | `(tactic| triv) => `(tactic| apply And.intro <;> triv)

example (x : α) (h : p) : x = x ∧ p := by
  triv
```

## Exercises (練習問題)

1. [3章 Propositions and Proofs (命題と証明)](./propositions_and_proofs.md) と [4章 Quantifiers and Equality (量化子と等号)](./quantifiers_and_equality.md) に戻り、タクティク証明を用いて出来るだけ多くの練習問題を解き直せ。``rw`` と ``simp`` も適切に使うこと。

2. タクティク結合子を使って、次の定理の証明を1行で書け:

```lean
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  admit
```
