# Introduction (イントロダクション)

## Computers and Theorem Proving (コンピュータと定理証明)

*Formal verification*(形式検証)では、論理的・計算的手法を使って、厳密な数学用語で表現された主張を立証する。この主張には、通常の数学の定理の他にも、ハードウェアやソフトウェアの一部、 ネットワークプロトコル、機械的・ハイブリッドシステムがその仕様を満たしているという主張も含まれる。実際には、数学的主張の検証をすることと、システムの正しさを検証することの間には、明確な区別はない。というのも、形式検証では、ハードウェアやソフトウェアのシステムを数学的な言葉で記述する必要があり、その時点で、その正しさに関する主張を立証することは、定理証明の一形態となる。逆に、数学の定理の証明には長い計算が必要な場合があり、その場合、定理の真偽を検証するには、その計算が想定通りに実行されることを検証する必要がある。

数学的な主張を裏付けるための最も信頼性のある方法は証明を与えることであり、20世紀の論理学の発展により、従来の証明方法のすべてではないにせよ、そのほとんどが、いくつかの基礎的な体系における小さな公理と規則の集合に還元できることが明らかになった。この還元のもとで、コンピューターが主張の立証に役立つ方法は2つある: 1つは、そもそも証明を「発見」する手助けをすること、もう1つは証明とされるものが正しいかどうかを「検証」する手助けをすることである。

*Automated theorem proving*(自動定理証明)は、この「発見」の側面に焦点を当てている。resolution theorem provers(導出原理に基づく証明器)、tableau theorem provers(タブロー定理証明器)、fast satisfiability solvers(高速充足可能性ソルバー)などは、命題論理や一階論理における公式の正しさを証明する手段を提供する。また、整数や実数に対する線形式や非線形式など、特定の言語や領域に対する探索手続きや決定手続きを提供するシステムもある。SMT(satisfiability modulo theories, 充足可能性モジュロ理論)のようなアーキテクチャは、領域一般的な探索手法と領域固有の手続きを組み合わせたものである。数式処理システムや高度な数学ソフトウェア・パッケージは、数学的計算を実行したり、数学的上界または下界を確立したり、数学的対象を見つけたりする手段を提供する。計算は証明と見なすこともでき、これらのシステムも数学的主張の立証に役立つ。

自動推論システムは、そのパワーと効率性を追求する結果、しばしば健全性の保証を犠牲にしている。このようなシステムにはバグがあることもあり、システムが導いた結果が正しいことを保証するのは難しい。対照的に、*interactive theorem proving*(対話型定理証明)は、定理証明の「検証」の側面に焦点を当て、全ての主張が適切な公理的基礎づけにおける証明によって保証されることを要求する。その基準は非常に高く、推論の全てのルールと計算の全てのステップは、それ以前の定義や定理に訴えることで正当化されなければならず、それら全ては最終的には基本的な公理や規則にまで遡る。実際、このようなシステムのほとんどは、他のシステムに伝達したり、独立にチェックしたりできる、完全に精緻化された「証明オブジェクト」を提供する。このような証明を構築するためには、通常ユーザーからの入力やインタラクションがより多く必要となるが、それによってより深く複雑な証明を得ることができる。

*Lean Theorem Prover*(Lean定理証明器)は、これら対話型定理証明と自動定理証明との間のギャップを埋めることを目的としている。このために、ユーザーとのインタラクションと完全に明記された公理的証明の構築が可能であるフレームワークの内部で、自動化されたツールと方法が使えるようにする。そのゴールは、数学的推論と複雑なシステムについての推論の両方をサポートし、両方の領域における主張を検証することである。

Leanの基礎となる論理は計算的解釈を持ち、Leanはプログラミング言語とみなすこともできる。もっと言えば、Leanは厳密な意味論を持つプログラムを書くためのシステムであり、プログラムが計算する関数について推論を行うためのシステムである。Leanはまた、独自の*metaprogramming language*(メタプログラミング言語)として機能するメカニズムを持つ。つまり、Leanそのものを使って自動化を実装したり、Leanの機能を拡張したりすることができる。Leanのこのような側面は、このチュートリアルの関連チュートリアルである[Programming in Lean 4](TBD)(訳者注: 原文ではリンク切れだが[Functional Programming in Lean](https://leanprover.github.io/functional_programming_in_lean/)のこと？)で深く解説されるが、システムの計算的側面はここでも登場するだろう。

## About Lean (Leanについて)

*Lean*プロジェクトは、2013年にMicrosoft Research RedmondのLeonardo de Mouraによって立ち上げられた、現在進行中の長期的な取り組みであり、自動化への潜在的可能性の多くは時間をかけて徐々に実現されるだろう。Leanは[Apache License 2.0](LICENSE)の下でリリースされている。これは寛容なオープンソースライセンスであり、他の人がコードと数学ライブラリを自由に利用し、拡張することを許可している。

Leanをあなたのコンピュータにインストールするには、[Quickstart](https://leanprover.github.io/lean4/doc/quickstart.html)にある指示を参照するのがよいだろう。LeanのソースコードとLeanのビルド方法は、[https://github.com/leanprover/lean4/](https://github.com/leanprover/lean4/)から入手できる。

このチュートリアルは、Lean 4として知られるLeanの現在のバージョンについて記述する。

## About this Book (この本について)

この本は、Leanで証明を記述し検証する方法を学ぶために意図されている。そのために必要な背景情報の多くは、Lean特有のものではない。まず最初に、Leanがベースにしている論理システムを学ぶ。これは*dependent type theory*(依存型理論)の一種で、通常の数学の定理のほとんどを証明するのに十分強力であり、またそれを自然な方法で行うのに十分な表現力を持っている。より具体的には、Leanは*Calculus of Constructions*として知られるシステムのうち、帰納型を持つものの一種に基づいている。Leanは依存型理論で数学的対象を定義し数学的主張を表現できるだけでなく、依存型理論を証明を書くための言語としても使用できる。

完全に詳述された公理的証明は非常に複雑であるため、定理証明の課題は、できるだけ多くの細部をコンピュータに埋めさせることである。[2章 Dependent Type Theory (依存型理論)](./dependent_type_theory.md)では、これを行う様々な方法を学ぶことができる。例えば、項の書き換えや、項や式を自動的に単純化するLeanの自動化手法などである。同様に、*elaboration*や*type inference*(型推論)の方法も、柔軟な代数的推論をサポートするために使うことができる。

最後に、システムとのコミュニケーションに使用する言語や、複雑な理論やデータを管理するためにLeanが提供するメカニズムなど、Lean特有の機能について学ぶ。

本文中には、以下のようなLeanのコード例が見られる:

```lean
theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
  fun hpq : p ∧ q =>
  have hp : p := And.left hpq
  have hq : q := And.right hpq
  show q ∧ p from And.intro hq hp
```

(訳者注: 以下の文章は、文章中にあるようにVS Codeのコマンドを用いて翻訳元英語版を開いた際の話だと思われます。)
この本を[VS Code](https://code.visualstudio.com/)の中で読んでいると、"try it!"というボタンが表示される。このボタンを押すと、コード例を正しくコンパイルするのに十分な周囲の非表示コードとともに、エディタにコード例がコピーされる。読者はコード例を自由に修正することができ、それに応じてLeanは読者が入力した結果をチェックし、継続的にフィードバックを提供する。この後の章を読み進めながら、自分でコード例を実行し、自分自身で書いたコードを試してみることをお勧めする。本書はVS Code上で「Lean 4: Open Documentation View」コマンドで開くことができる。

## Acknowledgments (謝辞)

This tutorial is an open access project maintained on Github. Many people have contributed to the effort, providing
corrections, suggestions, examples, and text. We are grateful to Ulrik Buchholz, Kevin Buzzard, Mario Carneiro, Nathan
Carter, Eduardo Cavazos, Amine Chaieb, Joe Corneli, William DeMeo, Marcus Klaas de Vries, Ben Dyer, Gabriel Ebner,
Anthony Hart, Simon Hudon, Sean Leather, Assia Mahboubi, Gihan Marasingha, Patrick Massot, Christopher John Mazey,
Sebastian Ullrich, Floris van Doorn, Daniel Velleman, Théo Zimmerman, Paul Chisholm, Chris Lovett, and Siddhartha Gadgil for their contributions.  Please see [lean prover](https://github.com/leanprover/) and [lean community](https://github.com/leanprover-community/) for an up to date list
of our amazing contributors.
