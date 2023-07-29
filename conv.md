# The Conversion Tactic Mode (変換タクティクモード)

タクティクブロックの内部では、``conv`` キーワードを使うと*conversion mode*(変換モード)に入ることができる。このモードでは、仮説やターゲットの内部、さらには関数抽象や依存関数型の内部を移動して、その部分項に書き換えや単純化のステップを適用することができる。

## 用語に関する注意

この節は翻訳に際して追加した節である。

変換モードにおいて、「ターゲット」とは項構築の目標となる型のこと**ではなく**、書き換え・単純化の対象のことである。また、「ゴール」は単に1つのターゲットを保持するためにある。

通常のタクティクモードでは、ターゲットは ``⊢`` の後に書かれる。一方で、変換タクティクモードでは、ターゲットは ``|`` の後に書かれる。

## Basic navigation and rewriting (基本的なナビゲーションと書き換え)

最初の例として、``example (a b c : Nat) : a * (b * c) = a * (c * b)`` を証明してみよう(このページで挙げる例は、他のタクティクを使えばすぐに解ける可能性があるため、多少作為的である)。素朴な最初の一手は、タクティクモードに入って ``rw [Nat.mul_comm]`` を試すことである。しかし、そうするとターゲット内の一番最初に登場する乗法について可換性が適用され、ターゲットが ``b * c * a = a * (c * b)`` に変換されてしまう。この問題を解決する方法はいくつかあるが、より正確なツールである変換モードを使用することは解決法の1つである。次のコードブロックでは、タクティクブロック内の各行の後に現在のターゲットを示している。

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    -- ⊢ a * (b * c) = a * (c * b)
    lhs
    -- ⊢ a * (b * c)
    congr
    -- 2 goals: ⊢ a, ⊢ b * c
    rfl
    -- ⊢ b * c
    rw [Nat.mul_comm]
```

上記のスニペット(小さなコード)では次の3つのナビゲーションコマンドを使っている:

- ``lhs`` は関係(ここでは等号)の左辺にターゲットを絞る。関係の右辺にターゲットを絞る ``rhs`` コマンドもある。
- 現在のターゲット内の先頭の関数(ここでは乗法)が(非依存的かつ明示的な)引数をとるなら、``congr`` は先頭の関数を分解し、各引数をターゲットとするゴールを引数の数だけ生成する。
- ``rfl`` は現在のターゲットを反射性を使って閉じ、次のゴールに移る。

目的のターゲットに到着したら、通常のタクティクモードと同様に ``rw`` を使うことができる。

変換モードを使う2つ目の主な理由は、束縛のスコープ内で部分項を書き換えることができるからである。例えば、``(fun x : Nat => 0 + x) = (fun x => x)`` を証明したいとしよう。素朴な最初の一手は、タクティクモードに入って ``rw [Nat.zero_add]`` を試すことである。しかし、これは失敗し、次のようなエラーメッセージを見ていらいらするだろう。

```
error: tactic 'rewrite' failed, did not find instance of the pattern
       in the target expression
  0 + ?n
⊢ (fun x => 0 + x) = fun x => x
```

正しい解法(の一例)はこうである:

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  conv =>
    lhs
    intro x
    rw [Nat.zero_add]
```

ここで、``intro x`` は ``fun`` の束縛スコープ内に入るナビゲーションコマンドである。この例は多少作為的であることを断っておく。この例は次のように解くこともできる:

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  funext x; rw [Nat.zero_add]
```

あるいは、``simp`` を使うだけでよい。

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  simp
```

``conv at h`` を使うと、現在のコンテキスト内の仮説 ``h`` を書き換えることもできる。

## Pattern matching (パターンマッチング)

上記のコマンドを使ったナビゲーションは面倒だと思うかもしれない。パターンマッチングを使えば、次のようにショートカットできる:

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in b * c => rw [Nat.mul_comm]
```

これは次の糖衣構文である:

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    pattern b * c
    rw [Nat.mul_comm]
```

もちろん、ワイルドカードも使える:

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in _ * c => rw [Nat.mul_comm]
```

## Structuring conversion tactics (変換タクティク証明の構造化)

``conv`` モード中も、タクティク証明を構造化するために波括弧と ``.`` を使うことができる。

```lean
example (a b c : Nat) : (0 + a) * (b * c) = a * (c * b) := by
  conv =>
    lhs
    congr
    . rw [Nat.zero_add]
    . rw [Nat.mul_comm]
```

## Other tactics inside conversion mode (変換モードにおける他のタクティク)

- ``arg i`` は現在のターゲットの ``i`` 番目の非依存的明示的引数にターゲットを絞る。

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    -- ⊢ a * (b * c) = a * (c * b)
    lhs
    -- ⊢ a * (b * c)
    arg 2
    -- ⊢ b * c
    rw [Nat.mul_comm]
```

- ``args`` は ``congr`` の別名である。

- ``simp`` は現在のターゲットに単純化子を適用する。``simp`` は通常のタクティクモードと同様のオプションをサポートする。

```lean
def f (x : Nat) :=
  if x > 0 then x + 1 else x + 2

example (g : Nat → Nat) (h₁ : g x = x + 1) (h₂ : x > 0) : g x = f x := by
  conv =>
    rhs
    simp [f, h₂]
  exact h₁
```

- ``enter [1, x, 2, y]`` は与えられた引数を使って ``arg`` と ``intro`` を繰り返す。これは単なるマクロである:

```
syntax enterArg := ident <|> group("@"? num)
syntax "enter " "[" (colGt enterArg),+ "]": conv
macro_rules
  | `(conv| enter [$i:num]) => `(conv| arg $i)
  | `(conv| enter [@$i:num]) => `(conv| arg @$i)
  | `(conv| enter [$id:ident]) => `(conv| ext $id)
  | `(conv| enter [$arg:enterArg, $args,*]) => `(conv| (enter [$arg]; enter [$args,*]))
```

- ``done`` は、もし未解決のゴールがあるなら失敗する。

- ``trace_state`` は現在のゴールの状態を表示する。

- ``whnf`` は現在のターゲットを*Weak Head Normal Form*(WHNF / 弱頭部正規形)に変換する。

- ``tactic => <tactic sequence>`` を使うと通常のタクティクモードに戻る。これは、``conv`` モードでサポートされていないタクティクでゴールを閉じるときや、従来の合同性や外延性の補題を適用するときに便利である。

```lean
example (g : Nat → Nat → Nat)
        (h₁ : ∀ x, x ≠ 0 → g x x = 1)
        (h₂ : x ≠ 0)
        : g x x + x = 1 + x := by
  conv =>
    lhs
    -- ⊢ g x x + x
    arg 1
    -- ⊢ g x x
    rw [h₁]
    -- 2 goals: ⊢ 1, ⊢ x ≠ 0
    . skip
    . tactic => exact h₂
```

- ``apply <term>`` は ``tactic => apply <term>`` の糖衣構文である。

```lean
example (g : Nat → Nat → Nat)
        (h₁ : ∀ x, x ≠ 0 → g x x = 1)
        (h₂ : x ≠ 0)
        : g x x + x = 1 + x := by
  conv =>
    lhs
    arg 1
    rw [h₁]
    . skip
    . apply h₂
```
