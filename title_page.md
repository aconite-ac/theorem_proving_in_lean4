# Theorem Proving in Lean 4

*by Jeremy Avigad, Leonardo de Moura, Soonho Kong and Sebastian Ullrich, with contributions from the Lean Community*

このテキストは読者がLean 4を使うことを前提にしています。Lean 4をインストールするには、[Lean 4 Manual](https://leanprover.github.io/lean4/doc/)の節[Setting
Up Lean](https://leanprover.github.io/lean4/doc/setup.html)をご覧ください。このテキストの最初のバージョンはLean 2用に書かれました。Lean 3用のバージョンは[こちら](https://leanprover.github.io/theorem_proving_in_lean/)で入手可能です。

## この翻訳について

*translated by aconite*(2章～12章)*, Haruhisa Enomoto*(1章)

この翻訳は有志による**非公式**翻訳です。翻訳に際して、表現を大きく変えた箇所や、分かりやすさを期すため記述やコード例を追加した箇所があります。また、用語の訳が一般的でない可能性があります。誤りを含む可能性もあります。必要に応じて原文[Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/) ([GitHub](https://github.com/leanprover/theorem_proving_in_lean4))もご覧ください。

原文のライセンスは[Apache License 2.0](https://github.com/leanprover/theorem_proving_in_lean4/blob/master/LICENSE)であり、それに基づいて原文を翻訳・公開しています。

この翻訳のソースは[GitHubリポジトリ](https://github.com/aconite-ac/theorem_proving_in_lean4)から入手可能です。また、ページ右上端のGitHubマークを押してGitHubリポジトリに移動することもできます。この翻訳の全ページとソースは[Apache License 2.0](LICENSE)の下で公開されています。

誤字脱字、内容の誤りの指摘、フォークからのPull Request、フォークによる翻訳の改変等は歓迎いたします。基本的に、ご指摘は[GitHubリポジトリのIssues](https://github.com/aconite-ac/theorem_proving_in_lean4/issues)で受け付けます。

mdBook付属の検索機能に関して、今のところ日本語検索は非対応です。お手数ですがページ内検索をご活用ください。章や節の名前、一部の専門用語は英語検索でヒットします。

翻訳に際して、機械翻訳サービス[DeepL翻訳](https://www.deepl.com/ja/translator)を参考にしました。
