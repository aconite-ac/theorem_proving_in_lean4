Introduction (イントロダクション)
============

## Computers and Theorem Proving (コンピュータと定理証明)

*formal verification*(形式的検証)には、論理的および計算的手法を用いて、正確な数学的形式言語で表現された主張を実証することが含まれる。形式的検証の対象には、通常の数学の定理だけでなく、ハードウェアやソフトウェア、ネットワークプロトコル、機械システムやハイブリッドシステムがそれらの仕様を満たしているという主張も含まれる。実際、数学の定理の検証とシステムの正しさの検証の間に明確な区別はない: 形式的検証ではハードウェアやソフトウェアのシステムを数学的形式言語で記述する必要があり、その時点でシステムの正しさに関する主張を実証することは定理証明の形式と同じになる。逆に、数学の定理を証明するには長い計算が必要な場合があり、そのような場合で定理の正しさを検証するには、その計算が期待通りのことをしていることの検証が必要となる。

数学的主張を裏付けるためのゴールドスタンダードは、その主張に証明を与えることである。20世紀における論理学の発展により、全てではないにしろほとんどの従来の証明手法が、いくつかの基礎体系のいずれかにおけるわずかな公理と規則に還元できることが示されている。この還元により、コンピュータは2つの方向性から主張の実証を支援することができる: 1つは未証明の定理の証明を見つける方向性、もう1つは正しいとされている証明が本当に正しいかどうかを検証する方向性である。

*automated theorem proving*(自動定理証明)は「見つける」側面に焦点を当てている。*resolution theorem provers*(導出原理に基づく定理証明器)、*tableau theorem provers*(タブローによる定理証明器)、*fast satisfiability solvers*(高速充足可能性ソルバー)などは、命題論理および一階述語論理における式の妥当性を証明する手段を提供する。整数あるいは実数上の線形または非線形な式など、特定の言語およびドメインに対する探索手続きや決定手続きを提供するシステムもある。*SMT*(satisfiability modulo theories)のようなアーキテクチャは、ドメイン一般的な検索方法とドメイン固有の手法を組み合わせている。*computer algebra system*(数式処理システム)と*specialized mathematical software packages*(分野特化数学ソフトウェアパッケージ)は、数学的計算の実行、数学的上界または下界の確立、数学的対象の探索の手段を提供する。計算は証明としてみなすこともできる。したがって、これらのシステムも数学的主張を実証するのに役に立つ。

自動推論システムはパワーと効率を追求するが、しばしば健全性の保証が犠牲になる。このようなシステムにはバグがある可能性があり、システムが提供した結果が本当に正しいことを確認することが難しい場合がある。対照的に、*interactive theorem proving*(対話型定理証明)は定理証明の「検証する」側面に焦点を当てており、システム内の全ての主張が適切な公理基盤における証明によって裏付けられていることを要求する。これは非常に高い基準である: 全ての推論ルールと全ての計算ステップは、事前の定義や定理に準拠して、さかのぼると基礎の公理と規則だけに準拠して、正当化される必要がある。実際、対話型定理証明システムのほとんどは、他のシステムに移行可能かつ独立にチェック可能な完全に精巧な「証明オブジェクト」を提供する。このような証明を構築するには、通常、ユーザーからのより多くの入力と対話が必要になるが、そのおかげで、より深く複雑な証明を得ることができるようになる。

*Lean Theorem Prover*(Lean 定理証明器)は、ユーザーとの対話と完全に記述された公理的証明の構築をサポートするフレームワークと、そのフレームワーク内で使うことのできるツールとメソッドにより、対話的な定理証明と自動定理証明の間のギャップを埋めることを目的としている。Leanの目標は、数学的推論と複雑なシステムに関する推論の両方をサポートし、両方の領域における主張を検証することである。

Leanの基礎となる論理は計算的解釈を持ち、Leanは通常のプログラミング言語と同等だと考えることができる。さらに言えば、Leanは、正確な意味論を備えたプログラムを作成し、またプログラムが計算する関数について推論するためのシステムだとみなすことができる。Leanには、独自の*metaprogramming language*(メタプログラミング言語)として機能するメカニズムもある。つまり、Lean自体を使って、Leanの自動化を実装したり、Leanの機能を拡張することができる。Leanのこれらの側面については、このテキストの関連チュートリアルである[Functional Programming in Lean](https://leanprover.github.io/functional_programming_in_lean/)で説明されている。この関連チュートリアルにはLeanの計算的側面が登場する。

## About Lean (Leanについて)

**Lean**プロジェクトは、2013年にMicrosoft Research RedmondのLeonardo de Mouraによって立ち上げられました。このプロジェクトは進行中かつ長期的な取り組みです。実現可能性のある自動化の多くは、時間をかけて徐々に実現されるでしょう。Leanは[Apache 2.0 license](./LICENSE)に基づいてリリースされています。Apache 2.0 licenseは、他者がコードと数学ライブラリを自由に使用および拡張できる寛容なオープンソースライセンスです。

Leanをコンピュータにインストールするには、[Quickstart](https://github.com/leanprover/lean4/blob/master/doc/quickstart.md)手順を参照してください。LeanのソースコードとLeanのビルド手順は、[https://github.com/leanprover/lean4/](https://github.com/leanprover/lean4/)で入手できます。

このチュートリアルは、Leanの現行バージョン、Lean 4について記述しています。

## About this Book (この本について)

この本の目的は、Leanで証明を記述および検証する方法を教えることである。この本の前半で学ぶ、Leanで証明を記述および検証するために必要な背景知識は、Leanに固有のものではない。まず、Leanの基礎となる論理体系を学ぶ。これは、従来の数学の定理のほとんど全てを証明するのに十分強力で、証明を自然な方法で行うのに十分な表現力を持つ、*dependent type theory*(依存型理論)の一つである。より具体的には、Leanは*Calculus of Constructions*として知られる帰納型を持つシステムの一つに基づいている。Leanは数学的対象を定義し、依存型理論で数学的主張を表現できるだけでなく、証明を書くための言語としても使用できる。

完全に詳述された公理的証明は非常に複雑であるため、定理証明支援系の課題はコンピュータにできるだけ多くの細部を埋めさせることである。この本を通じて、[依存型理論](./dependent_type_theory.md)の枠組みの中でこれをサポートするさまざまな方法、例えば、項書き換えや、項や式を自動的に単純化する自動メソッドなどを学ぶ。同様に、代数的推論の柔軟な形式をサポートする*elaboration*や*type inference*(型推論)の方法を学ぶ。

最後に、システムとの対話に使う言語や、複雑な理論やデータを管理するためにLeanが提供するメカニズムなど、Leanに固有の機能について学ぶ。

テキスト全体を通して、次のようなLeanコードの例が随所に示されている:

```lean
theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
  fun hpq : p ∧ q =>
  have hp : p := And.left hpq
  have hq : q := And.right hpq
  show q ∧ p from And.intro hq hp
```

[VS Code](https://code.visualstudio.com/)内でこの本を読んでいる場合は、"try it!"というボタンが表示される。ボタンを押すと、コードを正しくコンパイルするのに必要な前後のコードとともにサンプルがエディタにコピーされる。読者はエディタに入力して、コード例を変更することができる。Leanは入力結果をチェックして、継続的にフィードバックを提供する。以降の章を読み進めながら、コードサンプルを実行し、さらに自分自身のコードを使って実験することをお勧めする。コマンド「Lean 4: Open Documentation View」を使用すると、VS Codeでこの本を開くことができる。

## Acknowledgments (謝辞)

This tutorial is an open access project maintained on Github. Many people have contributed to the effort, providing
corrections, suggestions, examples, and text. We are grateful to Ulrik Buchholz, Kevin Buzzard, Mario Carneiro, Nathan
Carter, Eduardo Cavazos, Amine Chaieb, Joe Corneli, William DeMeo, Marcus Klaas de Vries, Ben Dyer, Gabriel Ebner,
Anthony Hart, Simon Hudon, Sean Leather, Assia Mahboubi, Gihan Marasingha, Patrick Massot, Christopher John Mazey,
Sebastian Ullrich, Floris van Doorn, Daniel Velleman, Théo Zimmerman, Paul Chisholm, Chris Lovett, and Siddhartha Gadgil for their contributions.  Please see [lean prover](https://github.com/leanprover/) and [lean community](https://github.com/leanprover-community/) for an up to date list
of our amazing contributors.
