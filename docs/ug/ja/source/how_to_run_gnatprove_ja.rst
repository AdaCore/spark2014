|GNATprove| の実行方法
======================

.. _ja Setting Up a Project File:

プロジェクトファイルの設定
-----------------------------------

基本的なプロジェクトの設定
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

まだ終わってなければ，GNATプロジェクトファイル（`.gpr`）を作成します．このプロジェクトファイルについては， |GNAT Pro| ユーザガイドの `GNAT Project Manager` の章を見て下さい．

GNAT Studio のプロジェクトウィザードを用いて，会話的にプロジェクトファイルを作成することもできます．メニューから :menuselection:`Project --> New...` をたどります．特に最初のオプション（ :menuselection:`Single Project` ）を見て下さい．

もし，素早く始めたいのであれば，かつ ``.ads/.adb`` という小文字のファイル名を用いた標準的な名前規則に従い，ソースコードを単一ディレクトリ中に格納します．プロジェクトファイルは次のようになります：

.. code-block:: gpr

  project My_Project is
     for Source_Dirs use (".");
  end My_Project;

これを ``my_project.gpr`` という名前で保存します．

コンパイルと検証に異なるスイッチを使う
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

場合によっては，GNAT や |GNATprove| に，異なったコンパイルレベルでのスイッチを渡したくなる場合があります．例えば，コンパイルのためだけに，同一プロジェクトファイル内で警告スイッチを用いるとします．この場合，コンパイルと検証で異なるスイッチを指定するために，シナリオ変数を利用することができます．

.. code-block:: gpr

  project My_Project is

    type Modes is ("Compile", "Analyze");
    Mode : Modes := External ("MODE", "Compile");

    package Compiler is
       case Mode is
          when "Compile" =>
             for Switches ("Ada") use ...
          when "Analyze" =>
             for Switches ("Ada") use ...
       end case;
    end Compiler;

  end My_Project;

上記のプロジェクトでは, ``Compile`` デフォルトモードを用いてコンパイルします::

  gprbuild -P my_project.gpr

形式検証は， ``Analyze`` モードを用い，次のようになります::

  gnatprove -P my_project.gpr -XMODE=Analyze

.. _ja Running GNATprove from the Command Line:

コマンドラインで |GNATprove| を使う
-----------------------------------------

|GNATprove| は，以下のようにコマンドラインで実行することができます::

    gnatprove -P <project-file.gpr>

ここでは，もっともよく使われるものの概要を示しています． なお， |GNATprove| は，プロジェクトファイルがないと実行できないことにご注意ください．

|GNATprove| が解析するファイルを選択するために，共通に用いられる 3つの方法があります．

* 全てを解析する::

     gnatprove -P <project-file.gpr> -U

  オプション ``-U`` を付けることで，プロジェクトツリー内の全てのプロジェクトの全てのユニットを解析します．まだ使用されていないユニットも含みます．

  これは，複雑なプロジェクトにおいて夜間に解析を実行したいときに通常用います．

* 指定したプロジェクトを解析する::

     gnatprove -P <project-file.gpr>

  指定プロジェクトの全てのメインユニットと，それらが依存している全てのユニット（これは再帰的に見つけます）を解析します．メインユニットが指定されていなければ，プロジェクト中の全てのファイルを解析します．

  特定の実行イメージのみの解析を行い時に用います．或いは，複雑なプロジェクト内部で，異なったオプションを持つ異なった実行イメージを解析したいときに用います．

* 単一ないしは複数ファイルを解析する::

     gnatprove -P <project-file.gpr> [-u] FILES...

  オプション ``-u`` を指定すると，指定したファイルのみを解析します．もし，このオプションが指定されないと，ファイルが依存している全てのユニットを再帰的に探し解析します．

  これは，日々のコマンドラインでの解析や， |GNATprove| を IDE によって利用する場合に用います．

|GNATprove| は，2 つの異なった解析を行います．フロー解析と証明です．フロー解析は，データフローに関係したアスペクト（ ``Global``, ``Depends``, ``Abstract_State``, ``Initializes`` およびこれらの洗練したバージョン）の正しさを検査し，また変数の初期化を検証します．証明は，実行時エラーがないこと，あるいは， ``Pre`` や ``Post`` アスペクトが示す表明の正しさを検証することです．スイッチ ``--mode=<mode>`` を用いることができ，モード（mode）には， ``check``, ``check_all``, ``flow``, ``prove`` , ``all`` があります．任意の解析を選択することができます．

* モード  ``check`` の場合， |GNATprove| は，プログラムが |SPARK| の制約を守っていることを部分的に検査します． ``check_all`` を使用する前に，このモードを使う利点は，フロー分析を必要としないので検査が高速になります．

* モード ``check_all`` の場合， |GNATprove| は，プログラムが |SPARK| の制約を守っていることを，全て検査します．関数に副作用がないといった，モード ``check`` では検査しない内容を含んでいます．即ち，モード ``check_all`` は，モード ``check`` を包含しています．

* モード ``flow`` では， |GNATprove| は，初期化していないデータをプログラムが入力とすることはない，規定したデータ依存あるいはフロー依存が実装において守られていることを検査します．モード ``flow`` は，モード ``check_all`` を包含しています．この段階は， *flow analysis （フロー解析）* と呼ばれます．

* モード ``prove`` では， |GNATprove| は，プログラムに実行時エラーがないこと，規定した関数契約が実装において遵守されていることを検査します．モード ``prove`` は，モード ``check_all`` を含んでおり，証明結果の十分性を保証するために，モード ``flow`` の機能の一つと同様に，初期化していないデータの読み込みがないことを検査します．この段階は， *証明（proof）* と呼ばれます．

* モード ``all`` はデフォルトのモードで， |GNATprove| はフロー解析と証明の双方を実行します．

オプション ``--limit-line=`` を使用することで，特定のファイルや Ada ファイル上の特定の行に証明を限定することができます．例えば，ファイル ``example.adb`` 上の 12 行目のみを証明したい場合， |GNATprove| の呼び出しにおいて， ``--limit-line=example.adb:12`` を付加することができます．オプション ``--limit-subp=`` を使用することで，特定のファイル上の特定の行で宣言されたサブプログラムのみを証明の対象とすることができます．オプション ``-j`` は，並列計算と並列証明を指示します．

証明のふるまいに影響を与える多数のオプションがあります．内部的には，オプション ``--prover`` によって規定された証明器は，各検査ないしは表明で繰り返し呼ばれます．オプション ``--timeout`` を用いることで，各検査や表明を証明するために各証明器に許容する最大時間を，変更することができます．オプション ``--steps`` を使用することで（デフォルト：100），証明器が動作を止める前に実行可能な最大の推論ステップ数を設定することができます． ``steps`` オプションは，確実な結果が必要なときには用いるべきです．というのは，タイムアウトによる結果は，計算機の能力や，現在の計算機負荷によって変化するからです．オプション ``-jnnn`` では，nnn に示す値が最大コア数として並列計算します．オプション ``-j0`` は，特別な意味を持ち，計算気が持つコア数を N としたときに，最大 N 並列で計算します．

.. note::

    プロジェクトがメインファイルを持つか，gnatprove に対して，あるファイルを開始点として指示する場合で，プロジェクト中の依存が線形である時（例えば，ユニットAは，ユニットBのみに依存していて，ユニットBは，ユニットCのみに依存しているといった場合）， ``-j`` スイッチを用いても，gnatprove は，ある時点では，一つのファイルのみを対象とします．この問題は，更に ``-U`` スイッチを用いることで避けることができます．

オプション ``--proof`` によっても，検証器に渡される検査方法もまた影響を受けます．デフォルトでは，証明器は，各検査毎あるいは表明毎に検査を実行します（モード ``per_check`` ）．これは，モード ``per_path`` を用いることで変わります．証明器は，検査における *path* 単位で検査を実行します．このオプションを用いると，通常時間が多くかかるようになります．なぜならば，証明器は何度も実行することになるからです．しかし，良い証明の結果を得ることができる場合があります．最後は，モード ``progressive`` です．このモードでは，一つの検査で一度だけ証明器を実行しますが，証明できない場合には，分離したパス毎に，異なる方法を用いて，少しずつ検査を行います．

オプション ``--proof`` とともに設定された証明モードは，修飾子 ``all`` 或いは ``lazy`` を用いて拡張することが可能です．完全なスイッチの表現は，例えば次のようになります： ``--proof=progressive:all`` ．この修飾子を用いることで，（時間を節約するために）証明できなかった最初の場所で検査を停止するか，或いは，（通常証明されていない式を正確に特定するため，次に手動で証明するかもしれない）同じ検査に関係した他の式を証明するように，証明を継続するかを選択できます．前者は，完全な自動証明に最も適していますし，これがデフォルト値となっています．また明示的に，修飾子 ``lazy`` として選択することもできます．後者は，自動証明と手動証明の組み合わせに最も適しています．修飾子 ``all`` で選択することができます．

証明の速度と能力に影響を与える個々のスイッチを設定する代わりに，スイッチ ``--level`` を用いることもできます．レベルとは，既定義の証明レベルであり，最も高速なレベル 0 （デフォルト値）から，最も強力なレベル 4 まであります．正確に言えば，各 ``--level`` の値は，これまでに示してきた他のスイッチを組み合わせたものと等価になります：

* ``--level=0`` は，次と等しい
  ``--prover=cvc4 --proof=per_check --timeout=1``
* ``--level=1`` は，次と等しい
  ``--prover=cvc4,z3,altergo --proof=per_check --timeout=1``
* ``--level=2`` は，次と等しい
  ``--prover=cvc4,z3,altergo --proof=per_check --timeout=5``
* ``--level=3`` は，次と等しい
  ``--prover=cvc4,z3,altergo --proof=progressive --timeout=5``
* ``--level=4`` は，次と等しい
  ``--prover=cvc4,z3,altergo --proof=progressive --timeout=10``

もし ``--level`` と重要なスイッチ ( ``--prover`` ， ``--steps`` または， ``--proof`` ) が, 同時に設定された場合は，後者が前者  ``--level`` の値を上書きします．

［注］ ``--level`` が同一でも，異なった計算機を使用した場合，結果が異なる場合があります．夜間のビルド（nightly builds）や，共有レポジトリでは， ``--steps`` or ``--replay`` スイッチを利用することを検討して下さい．証明に必要なステップ数は， ``--report=statistics`` オプションを付けて， |GNATprove| を実行することで得ることができます．

|GNATprove| は，静的解析ツール |CodePeer| を検査の証明に対する付加的な情報源として使用することを支援しています．このためには，コマンドラインで次を指定して下さい： ``--codepeer=on`` (詳細は次になります :ref:`ja Using CodePeer Static Analysis`)

デフォルトでは， |GNATprove| は，ユニットを単位として，変化していないファイルの再解析を行いません．このふるまいは，オプション ``-f`` により解除できます．

|GNATprove| は，ある項目を証明すると，結果をセッションファイルに保存します．ここには，要した時間と，証明までのステップが含まれます．この情報は，証明が正しかったということを確認するために，証明を再現するときに利用することができます． |GNATprove| を， ``--replay`` オプション付きで実行すれば，最後に証明したのと同じ証明器を使い，わずかに高い時間とステップ数で再現を試みます．このモードでは，ユーザが指示したステップ数と時間制約は無視されます．もし， ``--prover`` オプションがなければ， |GNATprove| は，全ての検査を試みます．そうでなければ，特定した証明器の一つによって証明された証明のみを再現します．全ての再現が成功すれば， |GNATprove| は，正常終了の場合と全く同様の出力を行います．もし再現が失敗すれば，関連する検査が，証明されなかったものととして報告されます．もし，関係する証明器が利用可能ではない（設定されていないサードパーティ製の証明器，あるいはユーザが ``--prover`` オプションを用いて他の証明器を選択した）場合は，証明を再現することができないという警告が発行されます．しかし，検査は依然として証明されたとマークされています．

デフォルトでは， |GNATprove| は，（Ada ないしは |SPARK| の規則違反により）エラーを検知した最初のユニットのところで停止します．オプション ``-k`` は， |GNATprove| が，複数ユニットで同種のエラーを発行するために用います．もし，Ada の規則違反があった場合は， |GNATprove| は解析を試みようとはしません． |SPARK| の規則違反があった場合は， |GNATprove| は，検査フェーズのあと停止し，フロー解析と証明を試みません．

エラーを検知したとき（検査によるメッセージ出力は含みません）， |GNATprove| は，非ゼロの終了ステータスを返します．エラーが検知されなければ， |GNATprove| は，警告がありそのメッセージを出力したとしても，ゼロの終了ステータスを返します．

GNAT ターゲット実行時ディレクトリを使用する
----------------------------------------------

もし，ターゲットコンパイラとして，GNAT を使用しており，用いているランタイムが， |GNATprove| のランタイムに含まれない場合，GNAT のインストール領域にある GNAT のランタイムを使用することができます．直接アクセスする，或いは |SPARK| のインストール領域にコピーすることによって可能となります．

ターゲットのGNAT ランタイムの場所を見つけるためには， ``<target>-gnatls -v`` コマンドを使用します． ``--RTS`` スイッチを使うと， ``gnatls`` を実行しているときに特定できます．

もし， |GNATprove| に渡される ``--RTS`` スイッチの引数が，正しい絶対ないしは相対ディクレトリ名ならば， |GNATprove| は，このディレクトリをランタイムディレクトリとして使用します．

正しくない場合， |GNATprove| は，既定義の場所で，ランタイムライブラリを探します．用いているランタイムの種類によって，２つのケースがあります．

* 完全なランタイム

  例えば， ``powerpc-vxworks-gnatmake`` をビルドコマンドとして使い， ``--RTS=kernel`` とするならば，次を使えます：

  .. code-block:: sh

    powerpc-vxworks-gnatls -v --RTS=kernel | grep adalib

  :file:`rts-kernel` ディレクトリを見つけ，このディレクトリを |SPARK| のインストール領域にコピーします．場所は次です． :file:`<spark-install>/share/spark/runtimes` コピーするためには，例えば，`bash` 構文を使うと次になります:

  .. code-block:: sh

    cp -pr $(dirname $(powerpc-vxworks-gnatls -v --RTS=kernel | grep adalib)) \
      <spark-install>/share/spark/runtimes

  もし，プロジェクトファイル中でまだ指定してなければ，次を加えます：

  .. code-block:: ada

     package Builder is
        for Switches ("Ada") use ("--RTS=kernel");
     end Builder;

  或いは，もし最近の GNAT と |SPARK| の版を使っているのであれば， `Runtime` プロジェクト属性経由で，ランタイムを指定できます：

  .. code-block:: ada

    for Runtime ("Ada") use "kernel";

* 構成可能なランタイム

  |SPARK| において，構成可能なランタイムを利用する最も単純な方法は， |SPARK| と，クロス GNAT コンパイラを同一のルートディレクトリにインストールすることです．

  その上で，プロジェクトファイル中に，Target と Runtime プロパティセットを記載すれば， |GNATprove| （バージョン 16.0.1以降）は，ランタイムを自動的に見つけることができます．例えば：

  .. code-block:: ada

     for Target use "arm-eabi";
     for Runtime ("Ada") use "ravenscar-sfp-stm32f4";

  もし，上記の単純な解決策が使えない場合は，次のコマンドを使って，GNAT構成可能ランタイムの場所を最初に見つける必要があります．

  .. code-block:: sh

     <target>-gnatls -v --RTS=<runtime> | grep adalib

  これによって次へのパスが分かります :file:`<runtime directory>/adalib`.

  次の例で，arm-eabiターゲットアーキテクチャ上の ravenscar-sfp-stm32f4 ランタイムライブラリを使うことを考えます．

  .. code-block:: sh

     arm-eabi-gnatls -v --RTS=ravenscar-sfp-stm32f4 | grep adalib

  このコマンドによって，次のファイルへのパスが分かります． :file:`<ravenscar-sfp-stm32f4 runtime>/adalib`

  次に <ravenscar-sfp-stm32f4 runtime> ディレクトリを |SPARK| インストール領域の :file:`<spark-prefix>/share/spark/runtimes` 以下にコピー（或いは，Unixにおいてはシンボリックリンクを作成）します．例えば， `bash` を用いると次のようになります．

  .. code-block:: sh

    cp -pr $(dirname $(arm-eabi-gnatls -v --RTS=ravenscar-sfp-stm32f4 | grep adalib)) \
      <spark-prefix>/share/spark/runtimes

  もし，プロジェクトファイルで指定していなければ，次をプロジェクトファイルに追加します．

  .. code-block:: ada

    for Runtime ("Ada") use "ravenscar-sfp-stm32f4";

.. _ja implementation_defined:

ターゲットアーキテクチャの指定と定義された実装のふるまい
----------------------------------------------------------------------

|SPARK| プログラムでは，曖昧さがないことが保証されます．それゆえ，プロパティの形式検証が可能となります．しかし，幾つかのふるまい（例えば， ``Size`` 属性のような表現属性値）は，利用するコンパイラに依存する場合があります．デフォルトでは， |GNATprove| は，GNATコンパイラと同じ選択をします． |GNATprove| は，また特別のスイッチを用いて他のコンパイラもサポートしています．

* ``-gnateT`` ターゲットの構成を指定するため
* ``--pedantic`` 定義された実装のあり得る振る舞いについての警告のため

［注］スイッチ ``--pedantic`` を用いても， |GNATprove| は，幾つかの定義された実装のふるまいを検出するのみです．

［注］|GNATprove| は，ベースタイプに対して，8bit の最小の倍数を常に選択します．Ada コンパイラにとっては，安全で保守的な選択となります．

.. _ja Target Parameterization:

ターゲットのパラメータ化
^^^^^^^^^^^^^^^^^^^^^^^^^^^

|GNATprove| は，コンパイルのターゲットは，そのコンパイラを実行しているホストと同じであると，デフォルトで仮定します．従って，ターゲットに依存する値，例えば，エンディアンや標準型のサイズやアライメントも同じであると考えます．もし， |GNATprove| を実行するホストとターゲットが異なる場合， |GNATprove| に対して，ターゲットを指定する必要があります．

［注］現在，プロジェクトファイル中の ``Target`` 属性は（何も出力されることなく）無視されます．

代わりに，以下をプロジェクトファイルに追加する必要があります:

.. code-block:: gpr

  project My_Project is
     [...]
     package Builder is
        for Global_Compilation_Switches ("Ada") use ("-gnateT=" & My_Project'Project_Dir & "/target.atp");
     end Builder;
  end My_Project;

ここで， ``target.atp`` は，プロジェクトファイル  ``my_project.gpr`` と同じディレクトリに保存されており，パラメータ化したターゲットの情報を含んでいます．このファイルの書式は， |GNAT Pro| ユーザガイドの ``-gnateT`` のスイッチ記述の箇所に記述されています．

パラメータ化したターゲット情報の目的は次になります．

* クロスコンパイルによって |GNATprove| が動作するホストとは異なるターゲットを記述するため．もし， |GNAT Pro| がクロスコンパイラであれば，ターゲットのためにコンパイラを呼び出すときに ``-gnatet=target.atp`` スイッチを用いることで，構成ファイルが生成されます．このスイッチを用いない場合は，ターゲットのためのファイルは手動で作成する必要があります．
* ホストとターゲットが同一であるときでも， |GNAT Pro| とは異なるコンパイラを使用している時には，そのパラメータを記述する必要があります．この場合，ターゲットファイルは，手動で作成する必要があります．


以下は，構成ファイルの例です．ここでは，PowerPC 750 プロセッサを持つベアボードで，ビッグエンディアンで構成しています::

  Bits_BE                       1
  Bits_Per_Unit                 8
  Bits_Per_Word                32
  Bytes_BE                      1
  Char_Size                     8
  Double_Float_Alignment        0
  Double_Scalar_Alignment       0
  Double_Size                  64
  Float_Size                   32
  Float_Words_BE                1
  Int_Size                     32
  Long_Double_Size             64
  Long_Long_Size               64
  Long_Size                    32
  Maximum_Alignment            16
  Max_Unaligned_Field          64
  Pointer_Size                 32
  Short_Enums                   0
  Short_Size                   16
  Strict_Alignment              1
  System_Allocator_Alignment    8
  Wchar_T_Size                 32
  Words_BE                      1

  float          6  I  32  32
  double        15  I  64  64
  long double   15  I  64  64

また，デフォルトでは， |GNATprove| は，ホストのランタイムライブラリを使用します．しかし，これは，クロスコンパイルをするときに，ターゲットにとって不適切かもしれません．スイッチ ``--RTS=dir`` を用いて， |GNATprove| を呼ぶことで，異なるランタイムライブラリを指定することができます．なお， ``dir`` は，デフォルトのランタイムライブラリの場所です．ランタイムライブラリの選択については， |GNAT Pro| ユーザガイドのツール ``gnatmake`` における ``--RTS`` スイッチの記述部分で説明しています．

.. _ja Parenthesized Arithmetic Operations:

括弧のついた算術演算
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Ada においては，括弧のつかない算術演算は，コンパイラによって演算順序が変更になる場合があります．このため，計算に失敗する場合もありますし（例えばオーバフロー検査によって），逆に成功する場合もあります．デフォルトでは， |GNATprove| は，全ての式を左から右に評価します．GNATも同様です．スイッチ ``--pedantic`` を用いると，計算順序が変更になった全ての演算に対して，警告が出力されます：

* それ自身が二項加算演算である二項加算演算（+,-）の被演算子
* それ自身が二項乗算演算である二項乗算演算（\*, /, mod, rem）の被演算子

.. _ja Using CodePeer Static Analysis:

CodePeer 静的解析器を使う
------------------------------

.. note::

   |CodePeer| は，SPARK Pro 17 以上の一部として利用可能です．しかし，SPARK Discovery には含まれていません．

|CodePeer| は，静的解析器であり，AdaCore社によって開発・商用化されました(http://www.adacore.com/codepeer)． |GNATprove| では，検査における証明において追加の情報源として， |CodePeer| を用いることができます．このためには，コマンドラインオプションとして， ``--codepeer=on`` を使用します． |CodePeer| は，自動証明の前に，実行されます．もし，特定の検査に関して証明ができた場合， |GNATprove| は，別の検証器を用いて，再度この検査を繰り返そうとはしません．

|GNATprove| を実行したとき， |CodePeer| は，解析のために，事前条件を生成しようとはせず，ユーザが記述した事前条件のみに基づいて動作します． |GNATprove| とともに用いたときの |CodePeer| 解析は，失敗しそうな検査を証明することができないという点において，確実にふるまいます． |CodePeer| は，厳格で契約に基づく解析を行う |SPARK| よりも，一般的により多くの証明を行うことができる可能性があります：

#. |CodePeer| は，サブプログラムのデータ依存に対して十分な近似を生成します．これは，サブプログラムの実装とサブプログラムに関係しているコールグラフ（call-graph）に基づいています． |CodePeer| は，従って，ユーザが示すデータ依存の情報が粗すぎて他の方法では演繹できないプロパティを証明することが可能です．

#. |CodePeer| は，ループにおけるループ不変条件の十分な近似を生成します． |CodePeer| は，従って，不十分なループ不変条件あるいはループ不変条件がないときに，他の方法では演繹できないプロパティを証明することができます．

加えて， |CodePeer| は，固定小数点の乗算および除算のまるめに関して，GNAT コンパイラと同様に動作します．結果的に，GNATでコンパイルしたコードの解析に対して，正確な結果を得ることができます．もし，ある固定小数点算術演算を行う他のコードが，GNAT以外のコンパイラでコンパイルしており，そのコードが固定小数点の乗算および除算をしているならば， |CodePeer| のまるめ方法とは異なっているかもしれません．その場合は， ``--codepeer=on``  は使うべきではありません．

|CodePeer| 解析は，浮動小数点演算を用いているコードを解析するときに特に有効です．というのは， |CodePeer| は，浮動小数点演算における限界値を証明するときに，高速かつ正確に動作するからです．

.. _ja Running GNATprove from GNAT Studio:

GNAT Studio で |GNATprove| を実行する
-----------------------------------------

GNAT Studio から |GNATprove| を実行できます． |GNATprove| がインストールされており，PATH上に存在するならば，以下に関して  :menuselection:`SPARK` メニューが使用可能になっています．

.. csv-table::
   :header: "サブメニュー", "アクション"
   :widths: 1, 4

   "Examine All",                "プロジェクト中の依存関係にある全てのメインとユニットに対して，フロー解析モードで， |GNATprove| を実行します．"
   "Examine All Sources",        "プロジェクト中の全てのファイルに対して，フロー解析モードで， |GNATprove| を実行します．"
   "Examine File",               "現在のユニットとそのボディ部および全てのサブユニットに対して，フロー解析モードで， |GNATprove| を実行します．"
   "Prove All",                  "プロジェクト中の依存関係にある全てのメインとユニットに対して， |GNATprove| を実行します．"
   "Prove All Sources",          "プロジェクト中の全てのファイルに対して， |GNATprove| を実行します．"
   "Prove File",                 "現在のユニットとそのボディ部および全てのサブユニットに対して， |GNATprove| を実行します．"
   "Show Report",                "|GNATprove| が生成したレポートファイルを表示します．"
   "Clean Proofs",               "|GNATprove| が生成した全てのファイルを削除します．"


三つの "Prove..." エントリは，プロジェクトファイルが示すモードで |GNATprove| を実行します．もし，モードが指定していなければ，デフォルトモードである "all" で実行します．

メニュー :menuselection:`SPARK --> Examine/Prove All` は，プロジェクト中の全てのメインファイルおよび依存している全てのファイル（依存は再帰的に調べます）に対して， |GNATprove| を実行します．ルートプロジェクトおよびルートプロジェクトに含まれるプロジェクトのメインファイルが対象です．メニュー :menuselection:`SPARK --> Examine/Prove All Sources` は，全てのプロジェクトの全てのファイルに対して， |GNATprove| を実行します．メインファイルを持っていない，或いは，他のプロジェクトを含んでいないプロジェクトの場合は，メニュー :menuselection:`SPARK --> Examine/Prove All` と :menuselection:`SPARK --> Examine/Prove All Sources` は同じになります．

メニュー項目のキーボードショートカットは，GNAT Studio の :menuselection:`Edit --> Key Shortcuts` を用いて設定することができます．

.. note::

   サブメニューによって表示されるパネルにおいて行った変更は，セッションが変わっても引き継がれます．チェックボックスやスイッチの選択が，前回と同様で良いかは，注意して確認する必要があります．

Adaファイルを編集するときに， |GNATprove| を，:menuselection:`SPARK` コンテキストメニューから実行することもできます．右クリックで，コンテキストメニューが表示されます．

.. csv-table::
   :header: "サブメニュー", "アクション"
   :widths: 1, 4

   "Examine File",       "現在のユニット，ボディ部，全てのサブユニットに対して，フロー解析モードで |GNATprove| を実行します．"
   "Examine Subprogram", "現在のサブプログラムに対してフロー解析モードで， |GNATprove| を実行します．"
   "Prove File",         "現在のユニット，ボディ部，全てのサブユニットに対して， |GNATprove| を実行します．"
   "Prove Subprogram",   "現在のサブプログラムに対して， |GNATprove| を実行します．"
   "Prove Line",         "現在の行に対して， |GNATprove| を実行します．"
   "Prove Check",        "現在の不合格となった条件に対して， |GNATprove| を実行します． |GNATprove| は，どの条件が不合格となったかを知るために，このオプションに対して少なくとも一回は動作します．"

メニュー :menuselection:`Examine File` と :menuselection:`Prove File` を除いて，他のサブメニューはまた総称体の内部のコードに対しても適用可能です．この場合，関係するアクションは，プロジェクト中の総称体の全てのインスタンスに対して適用されます．例えば，もしある総称体が 2 度インスタンス化されている時，総称体の内側のサブプログラムにおいて， :menuselection:`Prove Subprogram` を選択することで，総称体のインスタンス中の関連する2つのサブプログラムに対する証明を行います．

メニュー :menuselection:`SPARK --> Examine ...` は， |GNATprove| の解析のための種々の設定を行うパネルを開きます．このパネルにおいて，重要なのは解析モードの選択です．ここでは， ``check`` モード， ``check_all`` モード ``flow`` (デフォルト) から選択します．

メニュー :menuselection:`SPARK --> Prove ...` を選択すると， |GNATprove| を用いて解析を行うために用いる様々なスイッチを設定するためのパネルが開きます．デフォルトでは，このパネルには基本的な幾つかの設定がなされているのみです．例えば，証明レベルに関する設定があります（詳しくは， :ref:`ja Running GNATprove from the Command Line` 中の ``--level`` を参照方）． :menuselection:`Edit --> Preferences --> SPARK` において |SPARK| に対する ``User profile`` を ``Basic`` から ``Advanced`` に変更すると，証明のためのより複雑なパネルが表示されます．ここには，より詳細なスイッチがあります．

|GNATprove| プロジェクトのスイッチは，パネル ``GNATprove`` で変更することができます（ :menuselection:`Project --> Edit Project Properties --> Switches` )．

フロー解析および証明に関する検査を行ったときに，あるサブプログラムの特定の経路が不合格となった場合， |GNATprove| は，ユーザに対して経路情報を生成する場合があります．次の操作によって，ユーザは GNAT Studio 上にこの経路を表示することができます．最初の方法は，不合格を示す証明メッセージの左にあるアイコンをクリックすることです．二番目の方法は，エディタ中で関係する行の左にあるアイコンをクリックすることです．同じアイコンを再度クリックすると，経路は再び見えなくなります．

証明を用いて検証を行う検査に対して， |GNATprove| は，ユーザに対して反例も表示する場合があります（参照： :ref:`ja Understanding Counterexamples` ）．次の操作によって，ユーザは GNAT Studio 上にこの反例を表示することができます．最初の方法は，不合格を示す証明メッセージの左にあるアイコンをクリックすることです．二番目の方法は，エディタ中で関係する行の左にあるアイコンをクリックすることです．同じアイコンを再度クリックすると，反例は再び見えなくなります．

.. _ja Running GNATprove from GNATbench:

GNATbench から |GNATprove| を実行する
----------------------------------------------

|GNATprove| は，GNATbench から実行することができます． |GNATprove| がインストールされており，PATH上にある場合， :menuselection:`SPARK` メニューが表示され，その中には次の項目があります．

.. csv-table::
   :header: "サブメニュー", "アクション"
   :widths: 1, 4

   "Examine All",                "プロジェクト中の全てのメインとそれらが依存する全てのユニットに対して，フロー解析モードで |GNATprove| を実行します．"
   "Examine All Sources",        "プロジェクト中の全てのファイルに対して，フロー解析モードで |GNATprove| を実行します．"
   "Examine File",               "現在のユニット，そのボディ部，全てのサブユニットに対して，フロー解析モードで |GNATprove| を実行します．"
   "Prove All",                  "プロジェクト中の全てのメインとそれらが依存する全てのユニットに対して， |GNATprove| を実行します．"
   "Prove All Sources",          "プロジェクト中の全てのファイルに対して， |GNATprove| を実行します．"
   "Prove File",                 "現在のユニット，そのボディ部，全てのサブユニットに対して， |GNATprove| を実行します．"
   "Show Report",                "|GNATprove| が生成したレポートファイルを表示します."
   "Clean Proofs",               "|GNATprove| が生成した全てのファイルを削除します."

プロジェクトファイルで指定したモードで，3つの "Prove..." エントリを実行できます．もし，モードが指定されてなければ，デフォルトモードである "all" で，実行できます．

次のメニュー :menuselection:`SPARK --> Examine/Prove All` を選択することで，プロジェクト中の全てのメインファイルに対して， |GNATprove| が動作します．また，メインファイルが依存している全てのファイルも再帰的に調べられ，対象となります．ここでの全てのメインファイルとは，ルートプロジェクトおよびルートプロジェクトに含まれる全てのプロジェクト中に存在するメインファイルです． :menuselection:`SPARK --> Examine/Prove All Sources` は，全てのプロジェクト中の全てのファイルに対して， |GNATprove| を実行します．メインファイルも他のプロジェクトも含まないプロジェクトでは，メニュー :menuselection:`SPARK --> Examine/Prove All` と :menuselection:`SPARK --> Examine/Prove All Sources` は同等になります．

.. note::

   サブメニューにより表示されるパネル内で，ユーザが行った変更は，異なるセッションでも有効になります．以前に追加されたチェックボックスやスイッチの値が，今回も適切か否かと云うことを注意する必要があります．

Ada ファイルを編集しているときは，右クリックにより表示されるメニュー :menuselection:`SPARK` からも， |GNATprove| を実行することができます．

.. csv-table::
   :header: "サブメニュー", "アクション"
   :widths: 1, 4

   "Examine File",       "現在のユニット，ボディ部，サブユニットに対して，フロー解析モードで |GNATprove| を実行します．"
   "Examine Subprogram", "現在のサブユニットに対して，フロー解析モードで |GNATprove| を実行します．"
   "Prove File",         "現在のユニット，ボディ部，サブユニットに対して， |GNATprove| を実行します．"
   "Prove Subprogram",   "現在のサブプログラムに対して， |GNATprove| を実行します．"
   "Prove Line",         "現在の行に対して， |GNATprove| を実行します．"

.. _ja GNATprove and Manual Proof:

|GNATprove| と手動での証明
----------------------------

ある条件が妥当であるということを証明器が自動的に証明できなかった場合，手動により妥当性のための証明を試みることができます．

付録（Appendix）において，デフォルトである |GNATprove| とは異なった証明器を使う方法について，説明があります．

コマンドラインでの手動による証明
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

|GNATprove| が利用する証明器が，対話型として設定されている時，各解析条件ごとに次のようになる:

* 指定条件で初めて用いる場合．このとき，ファイル（指定した証明器に対する入力となる条件を含んでいる）がプロジェクト証明ディレクトリに作られます． |GNATprove| は，生成したファイル名とともに，この条件に関連したメッセージを出力します．条件を確認するために，ユーザは生成したファイルの編集が必要になる場合があります．

* 証明器を指定条件で一度用いており，編集可能なファイルが存在する場合．証明器は，このファイルとともに動作し，証明の成功・失敗を報告します．これはデフォルトの証明器と同様になります．

.. note::

   手動による証明のためのファイルを作成し，ユーザが編集した場合，検証器をそのファイルに基づいて実行するためには，もう一度，同一の検証器を |GNATprove| で指定する必要があります．条件が証明され，結果が一度 why3 セッションに保存されれば， |GNATprove| は，条件が妥当であるかを知るために，再度検証器を指定する必要はありません．

|GNATprove| を用いた解析では， ``--limit-line`` オプションを用いることで，単一の条件に限定することが可能です::

    gnatprove -P <project-file.gpr> --prover=<prover> --limit-line=<file>:<line>:<column>:<check-kind>

ここで， ``check-kind`` は，失敗した場合に |GNATprove| が出力するメッセージから推測できる文字列です．
以下の表を参照下さい．

.. UPDATES TO THIS TABLE SHOULD ALSO BE REFLECTED IN THE TABLE UNDER SECTION
.. "Description of Messages"

.. csv-table::
   :header: "Warning", "Check kind"
   :widths: 2, 1

   **run-time checks**
   "divide by zero might fail",                            "VC_DIVISION_CHECK"
   "array index check might fail",                         "VC_INDEX_CHECK"
   "overflow check might fail",                            "VC_OVERFLOW_CHECK"
   "range check might fail",                               "VC_RANGE_CHECK"
   "predicate check might fail",                           "VC_PREDICATE_CHECK"
   "predicate check might fail on default value",          "VC_PREDICATE_CHECK_ON_DEFAULT_VALUE"
   "length check might fail",                              "VC_LENGTH_CHECK"
   "discriminant check might fail",                        "VC_DISCRIMINANT_CHECK"
   "tag check might fail",                                 "VC_TAG_CHECK"
   "ceiling priority might not be in Interrupt_Priority",  "VC_CEILING_INTERRUPT"
   "interrupt might be reserved",                          "VC_INTERRUPT_RESERRED"
   "ceiling priority protocol might not be respected",     "VC_CEILING_PRIORITY_PROTOCOL"
   "task might terminate",                                 "VC_TASK_TERMINATION"

   **assertions**
   "initial condition might fail",                      "VC_INITIAL_CONDITION"
   "default initial condition might fail",              "VC_DEFAULT_INITIAL_CONDITION"
   "call to nonreturning subprogram might be executed", "VC_PRECONDITION"
   "precondition might fail",                           "VC_PRECONDITION"
   "precondition of main program might fail",           "VC_PRECONDITION_MAIN"
   "postcondition might fail",                          "VC_POSTCONDITION"
   "refined postcondition might fail",                  "VC_REFINED_POST"
   "contract case might fail",                          "VC_CONTRACT_CASE"
   "contract cases might not be disjoint",              "VC_DISJOINT_CONTRACT_CASES"
   "contract cases might not be complete",              "VC_COMPLETE_CONTRACT_CASES"
   "loop invariant might fail in first iteration",      "VC_LOOP_INVARIANT_INIT"
   "loop invariant might fail after first iteration",   "VC_LOOP_INVARIANT_PRESERV"
   "loop variant might fail",                           "VC_LOOP_VARIANT"
   "assertion might fail",                              "VC_ASSERT"
   "exception might be raised",                         "VC_RAISE"

   **Liskov Substitution Principle**
   "precondition might be stronger than class-wide precondition",               "VC_WEAKER_PRE"
   "precondition is stronger than the default class-wide precondition of True", "VC_TRIVIAL_WEAKER_PRE"
   "postcondition might be weaker than class-wide postcondition",               "VC_STRONGER_POST"
   "class-wide precondition might be stronger than overridden one",             "VC_WEAKER_CLASSWIDE_PRE"
   "class-wide postcondition might be weaker than overridden one",              "VC_STRONGER_CLASSWIDE_POST"

GNAT Studio での手動による証明
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

|GNATprove| を証明モードで実行した後，ローケーションタブ中の検査メッセージ上で右クリックするか，単一の条件の検査で失敗した行を右クリックすることによって（即ち，選択行に関して |GNATprove| は出力中に一つの検査のみを含んでいます），メニュー :menuselection:`SPARK --> Prove Check` を利用できるようになります．

ダイアログボックスの中の "Alternate prover (代替検証器)" では，Alt-Ergo とは異なる別の検証器を指定することができます．もし，別の検証器が，"interactive（会話的）"と指定され場合， :menuselection:`SPARK --> Prove Check` を実行することで，GNAT Studio は，手動による証明のためのファイルを開き，検証器に関係するエディタを立ち上げます．このエディタは，代替検証器の構成の中で指定されているものです．

いったんエディタが閉じられると，GNAT Studio は， :menuselection:`SPARK --> Prove Check` を再実行します．ユーザは，同じ代替検証器が以前と同様に指定されていることを確認してください．実行後，証明が失敗した場合，GNAT Studio は，再編集を要求します．
