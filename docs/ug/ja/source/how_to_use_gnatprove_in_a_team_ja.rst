.. _ja How to Use GNATprove in a Team:

|GNATprove| をチームで使う方法
================================

最も一般的な |GNATprove| 利用法は，チーム内での通常の品質管理ないしは品質保証アクティビティの一部としての利用です．通常， |GNATprove| を，現在のコードベースに対して毎晩実行します．開発者は，自分のコンピュータないしはサーバー上で昼間に |GNATprove| を実行します．この夜間と昼間の実行で得られた |GNATprove| の結果は，チームメンバで共有する必要があります．結果を見たり，新しい結果を共有している他の結果と比較します． |GNATprove| を実行し，結果を共有することで，様々なプロセスで利用することができます．

全てのケースで，ソースコードを（例えば共有ドライブ上で）直接に共有すべきではありません．この場合，ファイルのアクセス権や同時アクセスの問題を引き起こすことになります．従って，典型的な利用法としては，各ユーザがソースコードや環境をチェックアウトすることです．物理的に全てのユーザでソースコードを共有するのではなく，自分たちのソースコードのバージョン／コピーやプロジェクトファイルを使用します．

また，プロジェクトファイル中では常に，ローカル・非共有・書き込み可能ディレクトリをオブジェクトディレクトリとして指定します（明示的か暗黙的かに関わらず，オブジェクトディレクトリが存在しないと，プロジェクトファイルが置かれているディレクトリがオブジェクトディレクトリとして利用されます）．

幾つかのワークフロー
-----------------------

|GNATprove| をチームで利用するための幾つかのワークフローがあります．

1. |GNATprove| を，サーバないしはローカルで実行します．警告や検査メッセージは出力されないようにします．誤った警告を抑制し，証明されていない検査メッセージを正当化することで，可能となります．
2. |GNATprove| を，サーバないしはローカルで実行します．テキスト形式の結果を，構成管理で共有します
3. |GNATprove| を，サーバで実行します．結果を示すテキストを，サードバーティの品質計測ツール（例えば，GNATdashboard, SonarQube, SQUOREなど）に送ります
4. |GNATprove| を，サーバないしはローカルに実行します．その上で，|GNATprove| セッションファイルを，構成管理で共有します．

全てのワークフロー（最初のワークフローでは必須となりますが）において，メッセージを抑制し正当化することができます．全ての正当で完全な検証ツールと同様に，もちろん |GNATprove| が誤った警告をだすかもしれません．メッセージのタイプを見つけることが最初に必要です．

* 警告を抑制することができます．次を見て下さい． :ref:`ja Suppressing Warnings`
* 検査メッセージを正当化することができます．次を見て下さい． :ref:`ja Justifying Check Messages`

証明から得ることの出来る検査メッセージは，検証可能な検査とも関係しています．このためには，正しい契約 かつ／または 解析スイッチを見つけるために  |GNATprove|  とやりとりする必要があります．詳しくは次を見て下さい． :ref:`ja How to Investigate Unproved Checks`.

ワークフロー 3 におけるテキスト出力は，次のものと関係しています． |GNATprove| が出力するコンパイラのような出力で， ``--report`` スイッチと ``--warnings`` を用います（詳細については， :ref:`ja Running GNATprove from the Command Line` を参照下さい）．デフォルトでは，メッセージは証明に失敗した検査と警告に対してのみ発行されます．

ワークフロー 2 におけるテキスト出力は，上記のコンパイラのような出力と， |GNATprove| が生成するファイル ``gnatprove.out`` (詳細については次を参照して下さい :ref:`ja Effect of Mode on Output` 及び :ref:`ja Managing Assumptions`) 中の付加的情報です．

ワークフロー 4 は， 各ソースパッケージに対する形式検証の状態を記録するために， |GNATprove| が用いているセッションファイルを共有する必要があります．これは， Project Attributes 中に ``Proof_Dir`` 証明ディレクトリを記述し，このディレクトリを構成管理下で共有することにより得られます．衝突を避けるために，開発者は，このディレクトリにおける局所的な変更を構成管理に入れないことを推奨します．その代わり，定期的にディレクトリの更新されたバージョンを入出するようにします．例えば，サーバー上で夜間に実行するか，担当のチームメンバーが， |GNATprove| によって生成された最新のバージョンとともに証明ディレクトリを更新する責任者とすることができます．

他のワークフローと比較したときのワークフロー 4 のメリットは，すでに証明されているプロパティをローカルに再証明することを避けるという点にあります．共有セッションファイルは，証明された検証状態（Verification Conditions）の痕跡を保ち続けることができるからです．

.. _ja Suppressing Warnings:

警告を抑制する
--------------------

|GNATprove| は，2 種類の警告を発行し，別々に制御することができます．

* コンパイラの警告は，通常の GNAT コンパイラスイッチによって制御できます．

  * ``-gnatws`` 全ての警告を抑制する
  * ``-gnatwa`` 全ての付加的な警告を可能とする
  * ``-gnatw?`` 最後の文字によって示される特定の警告を可能とする

    詳細については |GNAT Pro| ユーザガイドを参照下さい．プロジェクトファイル中に記述されたコンパイルスイッチによって，コンパイラに渡すこともできます．

* |GNATprove| 特有の警告は， ``--warnings`` スイッチによって制御することができます．

  * ``--warnings=off`` 全ての警告を抑制する
  * ``--warnings=error`` 警告をエラーとして扱う
  * ``--warnings=continue`` 警告を発行するが，解析は停止しない（デフォルト）

    デフォルトでは |GNATprove| は，警告を出しますが，解析は停止しません．

ソースコード中で， ``Warnings`` pragma を用いることで，どちらのタイプの警告も選択的に抑制することができます．例えば， |GNATprove| は，手続き ``Warn`` 中で，3つの警告を発行するとします．これらはソースコード中で，3つの ``Warnings`` pragma を使用することで抑制できます．

.. literalinclude:: /gnatprove_by_example/examples/warn.adb
   :language: ada
   :linenos:

ここで ``Warnings Off`` pragma から開始し， ``Warnings On`` pragma ないしは関係するスコープの終了場所で囲まれた領域内で，特定のメッセージを持った警告を，抑制することができます． ``Reason`` 根拠文字列を使用することもできます．ある特定の形式を持った全ての警告を抑制するために，正規表現を用いて，特定のメッセージの代わりに与えることができます．プロジェクトの全てのユニットで横断的に，関連する警告を抑制するために，構成ファイル中に， ``Warnings Off`` pragma を加えることができます．特定のエンティティに ``Warnings Off`` pragma を指定することで，このエンティティに関係した全ての警告を抑制することができます．

この ``Warnings`` pragma は，GNAT コンパイラ或いは GNATprove に対してのみ適用することを示すために  ``GNAT`` 或いは ``GNATprove`` を第一引数にとることも可能です．

.. literalinclude:: /gnatprove_by_example/examples/warn2.adb
   :language: ada
   :linenos:

洗練したバージョンである ``Warnings`` pragma を用いることの利点は文書化という他に，スイッチ  ``-gnatw.w`` とともに用いることで，警告を全く抑制しない意味の無い ``Warnings`` pragma を見つけることができます．実際このスイッチは，コンパイル中は GNAT とともに使うことができ，形式検証中は，GNAT prove とともに使うことができます．これは， ``Warnings`` pragma をどちらかのツールのみに適用できることと同様です．

詳しくは， |GNAT Pro| 参照マニュアルをご覧下さい．

.. _ja Suppressing Information Messages:

情報メッセージを抑制する
--------------------------------

情報メッセージは，ソースコード中で，pragma ``Warnings`` を用いることで，警告と同様に，抑制することができます．

.. _ja Justifying Check Messages:

検査メッセージを正当化する
---------------------------

.. _ja Direct Justification with Pragma Annotate:

Annotate Pragma を用いた直接的正当化
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

|GNATprove| のフロー解析或いは証明により生成した検査メッセージは，ソースコード中に ``Annotate`` pragmaを追加することで，選択的に正当化できるようになります．例えば，return 文における潜在的なゼロ割についての検査メッセージは，次のように正当化することができます．

.. code-block:: ada

    return (X + Y) / (X - Y);
    pragma Annotate (GNATprove, False_Positive,
                     "divide by zero", "reviewed by John Smith");

pragma は次の形式を持ちます．

.. code-block:: ada

    pragma Annotate (GNATprove, Category, Pattern, Reason);

ここで，次のテーブル表現は，異なったエントリーについての説明です．

.. tabularcolumns:: |l|p{4.5in}|

.. csv-table::
   :header: "項目", "説明"
   :widths: 1, 4

   "GNATprove",   "固定の識別子である"
   "Category",    "``False_Positive`` か ``Intentional`` のいずれかである"
   "Pattern",     "正当化されるべき検査メッセージのパターンを記述した文字列リテラルである"
   "Reason",      "レビューのための正当化を提供する文字列リテラルである"

全ての論拠を示す必要があります．

項目 *Category* は現時点では，ツールのふるまいになんの影響も与えません．文書化の目的のみです．

* ``False_Positive`` は， |GNATprove| は証明できていませんが，検査が不合格ではないということを示します．

* ``Intentional`` 検査は不合格ですが，バグではないと考えていることを示しています．

*Pattern* は，正当化すべき検査メッセージの副文字列になります．

*Reason* は，正当化としてレビューに対してユーザが示す文字列です．この論拠（reason）は， |GNATprove| のレポート中に記載されます．

記載方法に関するルールは次の通りです．命令文リストないしは宣言文リスト中で， ``Annotate`` pragma は，リスト中の先行するアイテムに適用され，他の ``Annotate`` pragma を無視します．もし，先行するアイテムがない場合は，pragma は，内包構成要素に適用されます．例えば，if 文で，ガード条件が成立したときの処理（then-branch）における最初の要素がこの pragma であれば，if 文中のガード条件に適用されます．

もし先行するあるいは内包構成要素が，サブプログラムのボディ部である場合，pragma は，サブプログラムのボディ部と契約を含んでいる仕様部に適用されます．このことで，呼び出し元に関係しているとき，仕様部で |GNATprove| が出力する検査メッセージに対する正当化を行うことができます．

注意点としては，ソースコード中で，pragma ``Annotate`` の書かれたあと，極力広い範囲にわたって， pragma が適用されるということです．

* （新しい）pragma が，ブロック中の命令文リストに現れたときは，それがブロック全体（if文中では，全ての分岐を含む if ブロック内，ループ文の場合は，ループ文全体）に適用されることになります．
* pragma が，サブプログラムボディ部の先頭にあるとき，その pragma は，ボディ部全体とサブプログラムの仕様部に適用されます．

ユーザは，適切に， ``Annotate`` を記載すべきです．そうすべきではない検査を正当化しないように注意する必要があります．

.. literalinclude:: /gnatprove_by_example/examples/justifications.ads
   :language: ada
   :lines: 4-7


或いは，そのユニットのユーザにとって不可視である必要があるという実装時選択があるときは，ボディ部上で正当化を行います．

.. literalinclude:: /gnatprove_by_example/examples/justifications.ads
   :language: ada
   :lines: 9-10

.. literalinclude:: /gnatprove_by_example/examples/justifications.adb
   :language: ada
   :lines: 10-16

検査メッセージに対する正当化を行わない上記のような ``Annotate`` pragma 形式は，役に立たず， |GNATprove| は警告を発行します． |GNATprove| が発行する他の警告と同様に，この警告は， ``--warnings=error`` スイッチが設定された場合，エラーとして扱われます．

.. _ja Indirect Justification with Pragma Assume:

Pragma Assume による間接的正当化
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

|GNATprove| の証明によって生成される検査メッセージは，ソースコード中に， :ref:`Pragma Assume` を付加することによって，代替として間接的に正当化することができます．これによって，検査項目は証明されます．例えば，以下に示す割り当て文において整数オーバーフローの可能性に関する検査メッセージは，次のように正当化することができます．

.. literalinclude:: /gnatprove_by_example/examples/assumptions.adb
   :language: ada
   :lines: 8-13

pragma ``Assume`` は， ``Annotate`` pragma を利用するよりも強力です．このプロパティの仮定は，一つ以上の検査項目の証明に用いることができるからです．従って，単純な実行時検査を正当化するためには， ``Assume`` pragma を用いるよりも，一般的には， ``Annotate`` pragma を用いるべきです．以下の幾つかの例で ``Assume`` を使用することが望ましい場合を示します．

* 仮定を局所化するために：

  .. code-block:: ada

      pragma Assume (<External_Call's precondition>,
                     "because for these internal reasons I know it holds");
      External_Call;

  もし， ``External_Call`` の事前条件が変化した場合，仮定は引き続き論拠に対して有効であっても，ここでの仮定は有効ではなくなるかもしれません． ``External_Call`` の事前条件中の変化によって，ここで不整合が生じると， ``External_Call`` の証明ができなくなります．

* レビューを容易化するために，対象の外部から期待されていることをまとめておく：

  .. code-block:: ada

      External_Find (A, E, X);
      pragma Assume (X = 0 or (X in A'Range and A (X) = E),
                     "because of the documentation of External_Find");

  幾つかの progma ``Annotate`` を用いて情報を分散するよりも，たった一つの pragma ``Assume`` を用いる方が，保守やレビューが容易になります．もし，複数の場所で情報が必要ならば，pragma ``Assume`` を幾つかの手続きに分割します．

  .. code-block:: ada

      function External_Find_Assumption (A : Array, E : Element, X : Index) return Boolean
      is (X = 0 or (X in A'Range and A (X) = E))
      with Ghost;

      procedure Assume_External_Find_Assumption (A : Array, E : Element, X : Index) with
       Ghost,
       Post => External_Find_Assumption (A, E, X)
      is
         pragma Assume (External_Find_Assumption (A, E, X),
                        "because of the documentation of External_Find");
      end Assume_External_Find_Assumption;

      External_Find (A, E, X);
      Assume_External_Find_Assumption (A, E, X);

一般的に，仮定は可能な限り小さくすべきです（コードを動作させるための必要なもののみとする）．pragma ``Assume`` を用いた間接的正当化は，注意深く調べるべきです．なぜならば，検証プロセス中に容易にエラーを持ち込む可能性があるからです．

.. _ja Managing Assumptions:

仮定管理
--------------------

|GNATprove| は，サブプログラムとパッケージを別々に解析するので，その結果は，解析されないサブプログラムとパッケージに関する仮定に依存します．例えば，サブプログラムには実行時エラーがないという検証は，プロパティに依存します．このプロパティとは，呼び出している全てのサブプログラムにおいて実装済みの契約です．もし，あるプログラムが， |GNATprove| によって完全に解析されるならば，仮定の相互参照は，ほぼ自動的に行われます（いくつかの例外はあります．呼び出しの無限連鎖のために検査ができない場合です）．しかし，一般に，プログラムの一部は |SPARK| で記述され，他の部分は他の言語，多くは Ada, C, アッセンブリで記述されます．このように， |GNATprove| で解析することができない部分についての仮定は，他の手段（テスト・手動による解析・レビュー）で検証するために記録しておく必要があります．

スイッチ ``--assumptions`` が設定されたとき, |GNATprove| は，その結果ファイル ``gnatprove.out`` 中の残っている仮定についての情報を出力します．残っている仮定は，望む検証目的に適合するよう正当化するために必要です．サブプログラムについての仮定が生成されますが，様々なケースがあります．

* サブプログラムが解析されなかった（例えば， ``SPARK_Mode => Off`` と指定されていた）

* サブプログラムは， |GNATprove| で完全には解析されなかった（即ち，幾つかの検証されていない検査項目が残っている）

現在は，呼ばれるサブプログラムにおける仮定のみが出力され，呼び出しているサブプログラムの仮定が出力されないことに注意して下さい．

以下のテーブルは， |GNATprove| が出力するかもしれない仮定と，その主張の意味を説明しています．

.. tabularcolumns:: |l|p{4.5in}|

.. csv-table::
   :header: "仮定", "説明"
   :widths: 2, 4

    "effects on parameters and global variables", "サブプログラムは，仕様部（シグネチャ＋データ依存）に記述されているパラメータないしは広域変数以外の読み書きをしていない．"
    "absence of run-time errors", "サブプログラムには実行時エラーがない"
    "the postcondition", "サブプログラムの事後条件は，サブプログラムの各呼び出し後も保持されている"
