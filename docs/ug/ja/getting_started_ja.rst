.. _ja getting started:

****************************
|SPARK| を始めよう
****************************

新しいユーザが，　|SPARK| ツールを動かしてみるためのとても簡単な例から始めることにします．具体的に理解できるように，小さな |SPARK| プログラム例を用いています．

.. note::
   このユーザガイドは， |SPARK| ツールの最新の開発バージョンに対する説明です．もし，SPARK GPL 版を利用している場合，ここに記述している特徴の幾つかは利用できません．ツールとともに受け取った  |SPARK| ユーザガイドのバージョンを知るには，GNAT Studio と GNATbench IDE上で， :menuselection:`Help --> SPARK` を見るか， |SPARK| をインストールしたディレクトリから ``share/doc/spark`` をたどることで，バージョンが分かります．

|SPARK| ツールが，すでにインストールされていることが前提です．最低限必要なのは，次のツールです．

- |SPARK| Pro あるいは |SPARK| Discovery
- GNAT Studio 或いは the GNATbench plug-in (Eclipse用）

|SPARK| Pro は， |SPARK| の完全なツールセットです． |SPARK| Discovery は，サブセットですが，このユーザガイドにある全ての解析を実行することができます．もちろん， |SPARK| Pro がより強力です． |SPARK| Pro と比較したとき， |SPARK| Discovery は：

 * 自動証明器は，三つではなく一つになります
 * 静的解析器 |CodePeer| と統合されていません
 * 証明に失敗したときに反例が生成されません
 * モジュラー演算ないしは，浮動小数点演算を用いたプログラムに対する証明支援が限定的です

（注）厳密に言えば，GNAT Studio は必須ではありません． |SPARK| では，全てのコマンドはコマンドラインから実行できるからです．また，Eclipse の GNATbench プラグインを用いることもできます．しかし，この節では，GNAT Studio を前提として説明します．もし，サポートサービスを受けていれば，ツールのインストールに関する更なる情報を入手することができます．GNAT Tracker の "Download" タブにある，"AdaCore Installation Procedures" を見るか，より詳細な情報が必要であれば AdaCore 社に，お問い合わせ下さい．

例で用いる主要ツールは， |GNATprove| と GNAT Studio です．まずはじめに，新しいデフォルトプロジェクトとして GNAT Studio を立ち上げましょう．メニューバーに，:menuselection:`SPARK` メニューがあることを確認してください．

.. note::

   SPARK 2005 もお使いの場合，このメニューは， :menuselection:`SPARK 2014` の下にあります．これは，SPARK 2005 ツールセットの :menuselection:`SPARK` と区別するためです．

GNAT Studio で新しいファイルを開きます．下記の短いプログラムを入力し， ``diff.adb`` として保存して下さい．

.. literalinclude:: ../gnatprove_by_example/examples/diff.adb
   :language: ada
   :linenos:

このプログラムは， ``X`` と ``Y`` の差を計算し， ``Z`` に保存します．このことは， ``Depends`` アスペクトに現れています．即ち，Z の値は，入力パラメータである X と Y の値に依存しているということです．もちろん，お気づきのようにこのプログラムにはバグがあります．　``SPARK_Mode`` aspect を利用することで，このコードは， |SPARK| であることが分かり，ツールによって分析することができます．GNAT Studio のメニューから， :menuselection:`SPARK --> Examine File` を選んで下さい． |GNATprove| を，フロー解析モードで実行し，次のような報告を得ることができます：

.. literalinclude:: ../gnatprove_by_example/results/diff.flow
   :language: none

これらの警告は，プログラムの契約（ ``Z`` は， ``X`` と ``Y`` から計算する）と，その実装（ ``Z`` は， ``X`` だけから計算され， ``Y`` は使用しない）の間に違いがあることを示しています．この場合は，契約が正しくプログラムが間違っています．それで，割り当て式を，次のように変更します． ``Z := X - Y;`` もう一度，解析を実行します．今度は，何の警告もエラーを示しません．

プログラムにフローエラーがないことが分かったので，実行時エラーを検出するために，立証モードでツールを実行します．GNAT Studio のメニューから， :menuselection:`SPARK --> Prove File` を選び，結果ダイアログボックス中で， ``Execute`` をクリックします．|GNATprove| は，今度は，形式検証技術を用いて，プログラムには実行時エラーがないことを示そうと試みます．しかし，問題が見つかり，割り当て式を赤でハイライト表示します．次のように報告します．

..  correction version of diff.adb written in diff2.adb (to be able to use
..  automatic generation of output)

.. literalinclude:: ../gnatprove_by_example/results/diff2.prove
   :language: none

このレポートは，ある ``Natural`` 番号から，別の ``Natural`` を引いたときに，結果が ``Natural`` となることをツールが示すことはできない，ということを示しています．これは，あまり驚くことであってほしくはない！　この改善策にはいくつもの方法がありますが，それは要求次第です．ここでは，引数 ``Z`` の型を ``Natural`` から ``Integer`` に変更します．修正の上，再度解析を実行すると，今度は， |GNATprove| は，エラーも警告も出力しません．全ての検査を通過したので，このコードを実行しても，例外が送出されることはない，と確信を持てます．

この短い例によって， |SPARK| ツールを用いて行う解析とはどういうことか，という感じを分かってもらえたらと思っています．
