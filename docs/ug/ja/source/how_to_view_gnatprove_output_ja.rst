|GNATprove| の出力の見方
==============================

|GNATprove| には，2種類の出力があります．一つは，標準出力ないしはIDE (GPS ないしは GNATbench）に表示されるものであり，もう一つは， ``gnatprove.out`` ファイルに出力されます．このファイルは，プロジェクトのオブジェクトディレクトリのサブディレクトリ ``gnatprove`` の中にあります．

.. _ja The Analysis Results Summary Table:

解析結果サマリーテーブル
----------------------------------

ファイル ``gnatprove.out`` の最初にあるサマリーテーブルは，プロジェクトの全ての検査に対して，検証した結果の概要を示しています．テーブルは例えば次のようになっています．::

      ----------------------------------------------------------------------------------------------------------------
      SPARK Analysis Results      Total        Flow   Interval                          Provers   Justified   Unproved
      ----------------------------------------------------------------------------------------------------------------
      Data Dependencies               .           .          .                                .           .          .
      Flow Dependencies               .           .          .                                .           .          .
      Initialization               2100        2079          .                                .           .         21
      Non-Aliasing                    .           .          .                                .           .          .
      Run-time Checks               596           .          .    480 (altergo  31%, CVC4  69%)           .        116
      Assertions                      3           .          .      3 (altergo  33%, CVC4  67%)           .          .
      Functional Contracts          323           .          .    168 (altergo  24%, CVC4  76%)           .        155
      LSP Verification                .           .          .                                .           .          .
      ----------------------------------------------------------------------------------------------------------------
      Total                        3022  2079 (69%)          .                        651 (22%)           .   292 (9%)

サマリーテーブルの各行は，以下の意味を持ちます:

.. tabularcolumns:: |l|p{5in}|

.. csv-table::
   :header: "行記述", "説明"
   :widths: 1, 5

   "Data Dependencies", ":ref:`ja Data Dependencies` とパラメータモードの検証"
   "Flow Dependencies", ":ref:`ja Flow Dependencies` の検証"
   "Initialization", ":ref:`ja Data Initialization Policy` の検証"
   "Non-Aliasing", ":ref:`ja Absence of Interferences` の検証"
   "Run-time Checks", "実行時エラーがないことを検証（Verification of absence of run-time errors (AoRTE) (``Storage_Error`` の送出を除く)）"
   "Assertions", "Assertion Pragmas の検証"
   "Functional Contracts", "機能的契約の検証 (:ref:`ja Subprogram Contracts`, Package Contracts と Type Contracts を含む)"
   "LSP Verification", "Object Oriented Programming and Liskov Substitution Principle （オブジェクト指向プログラムとLiskov の代替原則）関連の検証"

テーブルの各カラムの意味は次の通りです．

* ``Total`` カラムは，このカテゴリに含まれる総検査数を示します．

* ``Flow`` カラムは，フロー解析によって証明された検査の数を示します．

* ``Interval`` カラムは，副式 [#f1]_ の型限界に基づき，単純な浮動小数点表現の静的境界解析による検査（オーバーフローと範囲検査）の検査数を記述します．

* ``Provers`` カラムは，自動ないしは手動による検証器によって証明された検査の数を記載しています．このカラムには，用いた検証器の情報および各検証器によって証明された検査の割合が記載されます．ある検査項目が複数の検証器によって証明される場合があることに注意して下さい．従って，ここでは数ではなく割合を用いています．最初に実行する検証器（コマンドラインスイッチ  ``--prover`` によって定まります）が，一般的には最も多くの検証項目を証明することにも注意して下さい．各検証器は，他の検証器によってすでに証明された検査項目に関しては呼び出されないからです．検証器の（使用）率は，アルファベット順で示します．

*  ``Justified`` カラムは，ユーザが提供した :ref:`ja Direct Justification with Pragma Annotate` に対する検査項目の数を示します．

* 最後に， ``Unproved`` カラムは，証明も正当化もしていない検査項目の数を示します．

.. rubric:: Footnotes
.. [#f1] いま，式が 3 * X / 4 だとすると，3 * X は副式の一つ．検査は，最終的な式の値ではなく，副式レベルでも行う

.. _ja Categories of Messages:

メッセージのカテゴリ
----------------------

|GNATprove| のメッセージには幾つかの種類があります．エラー，警告，検査，情報メッセージです．

* 次の場合にはエラーを出力します． |SPARK| 或いは他言語の規約違反や，解析を継続することができない問題が発生した場合です．エラーを抑止することはできません．解析を進めるためには，エラー指摘箇所を修正する必要があります．

* 警告は，変数の未使用の値，意味のない値の割り当て等の疑わしい状況に対して発行されます．警告は， ``"warning: "`` という接頭辞が付きます． ``pragma Warnings`` pragma によって，抑止可能です．詳しくは， :ref:`ja Suppressing Warnings` を参照下さい．

* 検査メッセージは，プログラムの正しさに影響を与えるかもしれないコードが持つ潜在的な問題がある場合に，発行されます．例えば，初期化忘れ，実行時検査の潜在的な不合格，証明されていない表明などです．検査メッセージは，重大さに関する情報を含んでいます．重大さに従って，メッセージテキストには，次の接頭辞がつきます．  ``"low: "``, ``"medium: "`` , ``"high: "`` です．検査メッセージは警告のように抑制することができません．しかし， pragma  ``Annotate`` を用いて，個々には各メッセージを正当化することができます．詳しくは次の節を参照して下さい :ref:`ja Justifying Check Messages`

* 情報メッセージは，ユーザに |GNATprove| がある構成要素に関して限界があることを通知します．或いは， |GNATprove| の出力を誤解することを防ぐために通知します．また， |GNATprove| の幾つかのモードにおいて証明された検査に関しての報告としても発行されます．

.. _ja Effect of Mode on Output:

出力におけるモードの影響
------------------------

|GNATprove| を，4つの異なったモードで実行することができます．次のスイッチを指定します: ``--mode=<mode>`` ここで，可能なモードの値としては， ``check``, ``check_all``, ``flow``, ``prove``, ``all`` があります（詳細については，次を参照して下さい :ref:`ja Running GNATprove from the Command Line`)．出力は選択したモードに依存します．

モード ``check`` あるいはモード ``check_all`` を選択した場合， |GNATprove| は， ``SPARK_Mode`` が ``On`` である全てのコードにおいて， |SPARK| の制約に違反しているエラーメッセージのリストを標準出力に出力します．

モード ``flow`` とモード ``prove`` を選択した場合， この検査は最初のフェーズで実行されます．

モード ``flow`` では， |GNATprove| は，初期化されていないデータの読み込みの可能性，データ依存・フロー依存と仕様と実装の不整合，使用していない値の割り当てやリターン文の不足といった疑わしい状況に対して，標準出力にメッセージを出力します．これらのメッセージは，全てフロー解析に基づいて作成されます．

モード ``prove`` では， |GNATprove| は，初期化されていないデータの読み込みの可能性（フロー解析を使用する），潜在的な実行時エラーおよび特定の機能契約と実装との不整合（証明を使用する）に対するメッセージを標準出力に出力します．

モード ``all`` では， |GNATprove| は， ``flow`` モードおよび ``prove`` モード双方のメッセージを標準出力に出力します．

もし ``--report=all``, ``--report=provers`` , ``--report=statistics`` のいずれかのスイッチが指定された場合， |GNATprove| は，追加で，証明された検査項目に対する情報メッセージを標準出力に出力します．

|GNATprove| は， ``gnatprove.out`` ファイル中に広域プロジェクト統計情報を出力します．この情報は，メニュー  :menuselection:`SPARK --> Show　Report` を用いて，GPS 上に表示することが可能です．統計情報は以下になります．

* どのユニットを解析したか（フロー解析，証明，或いは双方）
* これらユニットのうちどのサブプログラムが解析されたか（フロー解析，証明，或いは双方）
* この解析の結果

メッセージの記述
-----------------------

この節では， |GNATprove| が出力する可能性のあるメッセージの違いをリスト化します．各メッセージは，ソースコード中の正確な場所を示します．例えば，もし，ソースファイル ``file.adb`` が下記のような割り算を持つ場合::

      if X / Y > Z then ...

|GNATprove| は，（例えば）次を出力します::

   file.adb:12:37: medium: divide by zero might fail

ここで，割り算記号 ``/`` の位置は，12行目の37カラムであり正確な記述となっています．以下の最初のテーブルの説明を見て下さい．割り算検査は，除数がゼロではないことを検証します．つまり，このメッセージは， ``Y`` に関するものであり， |GNATprove| は，それがゼロとはなり得ないことを証明できません．以下の表中の説明は，ソースコード上の位置とともに解釈する必要があります．

以下の表における説明では，証明によって発行される検査メッセージの種類を示しています．

.. UPDATES TO THIS TABLE SHOULD ALSO BE REFLECTED IN THE TABLE UNDER SECTION
.. "Manual Proof in Command Line"

.. tabularcolumns:: |l|p{3in}|

.. csv-table::
   :header: "メッセージ種別", "説明"
   :widths: 1, 4

   **run-time checks**
   "divide by zero", "割り算・mod・rem 演算子の第二被演算子が，ゼロでないことを検査する [#msgdes1]_ "
   "index check", "インデックスが配列の境界内であることを検査する"
   "overflow check", "算術演算が基本型の境界内であることを検査する"
   "range check", "値が，期待されるスカラーサブタイプの境界内であることを検査する"
   "predicate check", "値が，適用可能な型述語を満足しているかどうかを検査する [#msgdes2]_ "
   "predicate check on default value", "型に対するデフォルト値が，適用可能な型述語を満足しているかを検査する"
   "length check", "配列は，適切な配列副型の配列長であるかを検査する．"
   "discriminant check", "区別記録型（discriminant record) [#msgdes3]_ の区別子（discriminant）が，適切な値を持っているかを検査する．変異記録型の場合，記録型のフィールドに対する単純なアクセスに対して生じる．しかし，区別子の固定値が必要となる場合もある [#msgdes4]_ "
   "tag check",          "タグ付きオブジェクトのタグが適切な値を持っているかの検査をする [#msgdes5]_ "
   "ceiling priority in Interrupt_Priority", "Interrupt_Priority 中で，アスペクト Attach_Handler を持っている手続きを含む保護オブジェクト [#msgdes6]_ に設定された上限優先度を検査する"
   "interrupt is reserved",   "Attach_Handler に設定された割り込みが予約されていないことを検査する"
   "ceiling priority protocol", "上限優先度プロトコルの利用が適切かを検査する．即ち，タスクが保護操作を呼び出した時，タスクの有効な優先度が，保護オブジェクトの優先度より高くない (ARM Annex D.3)"
   "task termination",   "タスクが終了しないことを検査で示す．これはRavenscar [#msgdes7]_ で必要とされている．"

   **assertions**
   "initial condition", "実行時準備処理 (elaboration) の後で，パッケージの初期状態が真であることを検査する．"
   "default initial condition", "型のデフォルトの初期状態が，その型のオブジェクトに対してデフォルトの初期化を行ったのちも True であることを検査する．"
   "precondition", "指定した呼び出しの事前条件アスペクトが True と評価できるかを検査する．"
   "call to nonreturning subprogram", "エラー時に呼び出されるサブプログラム呼び出しが不達であることを検査する．"
   "precondition of main", "メイン手続きの事前条件アスペクトが，実行時準備処理 (elaboration) ののちに True であることを検査する．"
   "postcondition", "サブプログラムの事後条件アスペクトが，True であることを検査する．"
   "refined postcondition", "サブプログラムの洗練事後条件(refined postcondition)が，True であることを検査する．"
   "contract case", "サブプログラムの終端において，契約ケースが True であることを検査する．"
   "disjoint contract cases", "契約ケース aspect の各ケースが，全て互いに素であることを検査する"
   "complete contract cases", "契約ケース aspect の各ケースにより，事前条件アスペクトによって認められている状態空間がカバーされていることを検査する．"
   "loop invariant in first iteration", "ループにおける最初の繰り返しでループ不変条件が真となることを検査する．"
   "loop invariant after first iteration", "ループにおける初回に続く繰り返しで，ループ不変条件が真となることを検査する．"
   "loop variant", "与えられたループ変数が，ループの各繰り返しで，指定したとおり減少／増加することを検査する．これは，ループの終了に関係する．"
   "assertion", "表明が真となることを検査する．"
   "raised exception", "エラーを送出する文には到達しないことを検査する．"

   **Liskov Substitution Principles**, " [#msgdes8]_ "
   "precondition weaker than class-wide precondition", "サブプログラムの事前条件 aspect が，クラスレベルの事前条件よりも弱い条件となっていることを検査する"
   "precondition not True while class-wide precondition is True", "もし，クラスレベルの事前条件が True であるならば，サブプログラムの事前条件 aspect が，True であることを検査する．"
   "postcondition stronger than class-wide postcondition", "サブプログラムの事後条件 aspect が，クラスレベルの事後条件よりも強い条件であることを検査する．"
   "class-wide precondition weaker than overridden one", "サブプログラムのクラス全体の事後条件 aspect が，オーバライドされたクラスレベルの事前条件よりも弱い条件であることを検査する．"
   "class-wide postcondition stronger than overridden one", "サブプログラムのクラス全体の事後条件が，オーバライドされたクラスレベルの事後条件よりも強い条件であることを検査する．"

.. rubric:: Footnotes
.. [#msgdes1] mod と rem はともに剰余演算子．負数の振る舞いが異なる．
.. [#msgdes2] 型述語とは以下のように，副型を規定するための述語表現．
  type Prime is new Positive with
  Predicate => (for all Divisor in 2 .. Prime / 2 => Prime mod Divisor /= 0);
.. [#msgdes3] パラメータ化された記録型
.. [#msgdes4] 区別記録型の特別な形式
.. [#msgdes5] タグ付き型（tagged）．オブジェクト指向における継承に類似した仕組みを実現するための形式
.. [#msgdes6] 保護型（protected type）は，排他的にデータにアクセスすることを保証する．複数タスクによるデータへのアクセス等で使用する
.. [#msgdes7] Ravenscar profile は，セーフティクリティカルおよびリアルタイムシステムのために Ada タスキングのサブセットを定義したもの
.. [#msgdes8] 「Liskov 代替原則」の Liskov は，抽象データ型を最初に実装した CLU の設計者として知られる Barbara Liskov 氏にちなむ．
.. insert blank line to separate more clearly the two tables in the HTML output

|

次のテーブルは，全てのフロー解析メッセージを示しています．クラスの記号の意味は次の通りです．E: エラー
W: 警告 C: 検査

.. tabularcolumns:: |p{3in}|l|p{3in}|

.. csv-table::
   :header: "メッセージ種別", "クラス", "説明"
   :widths: 1, 1, 6

   "aliasing", "E", "2つの形式的あるいは広域的パラメータが別名化している．"
   "function with side effects", "E", "副作用を持つ関数が検知された．"
   "cannot depend on variable", "E", "特定の式（例えば，区別仕様やコンポーネント宣言）においては，変数に依存してはいけない．"
   "missing global", "E", "フロー解析が，広域或いは初期化アスペクトで記載のない広域変数を検知した．"
   "must be a global output", "E", "フロー解析は，in モードの広域変数の更新を検知した．"
   "pragma Elaborate_All needed", "E", "リモート状態抽象が，パッケージの実行時準備処理中に用いられた．Elaborate_All がリモートのパッケージ対して必要となる．"
   "export must not depend on Proof_In", "E", "Proof_Inとマークされている定数に依存しているサブプログラムの出力を検知した．"
   "class-wide mode must also be a class-wide mode of overridden subprogram", "E", "オーバライドしているサブプログラムの広域契約とオーバライドされているサブプログラムの広域契約間での不適合がある．"
   "class-wide dependency is not class-wide dependency of overridden subprogram", "E", "オーバライドしているサブプログラムの依存契約とオーバライドされているサブプログラムの依存契約間に不適合がある．"
   "volatile function", E, "非 volatile 関数は，広域 volatile 変数を持たない場合がある．"
   "tasking exclusivity", E, "二つのタスクが，同一の保護オブジェクト或いは同一の保留オブジェクト(suspension object) に関してサスペンドしない．"
   "tasking exclusivity", E, "2つのタスクが，同一の非同期オブジェクトに対して読み書きをしない．"
   "missing dependency", "C", "依存関係にあるにもかかわらず，依存が示されていない．"
   "dependency relation", "C", "出力パラメータないしは広域変数が，依存関係に示されていない．"
   "missing null dependency", "C", "変数に対する NULL 依存の記述がない．"
   "incorrect dependency", "C", "状態依存が十分に記述されていない．"
   "not initialized", "C", "フロー解析によって，初期化されていない変数が見つかった．"
   "initialization must not depend on something", "C", "誤った初期化アスペクトが検知された．"
   "type is not fully initialized", "C", "デフォルトで初期化する指定をしている型が，初期化されていない．"
   "needs to be a constituent of some state abstraction", "C", "何らかの状態抽象を通して示すべき構成要素を，フロー解析が検知した．"
   "constant after elaboration", "C", "実行時準備処理後，定数であるべきオブジェクトは，実行時準備処理後にその値を変更してはいけないし，他のサブプログラムの出力とはなりえない．"
   "is not modified", "W", "変数が in out モードで宣言されているにも関わらず，決して修正されないならば，in モードで宣言することができる．"
   "unused assignment", "W", "フロー解析が，割り当て後，決して読み出されることのない変数への割り当てを検知した．"
   "initialization has no effect", "W", "初期化済みだが，読み出されることのないオブジェクトを，フロー解析が検知した"
   "this statement is never reached", "W", "この文は決して実行されない（デッドコード）．"
   "statement has no effect", "W", "フロー解析は，プログラムに影響を与えない文を検知した．"
   "unused initial value", "W", "out, in out パラメータ或いは広域変数に影響を与えない，in ないしは in out パラメータおよび広域変数を見つけた．"
   "unused", "W", "広域的に或いは局色的に宣言された変数が使用されていない．"
   "missing return", "W", "リターン文が関数に存在していない可能性がある．"
   "no procedure exists that can initialize abstract state", "W", "フロー解析が初期化不能な状態抽象を検知した．"
   "subprogram has no effect", "W", "出力をしないサブプログラムを検知した．"
   "volatile function", E, "volatile 広域変数を持たない volatile 関数を volatile とする必要がない．"

.. note::

   フロー解析が出力するメッセージには，エラーに区分されるものがあり，これは抑制したり正当化することができない．

.. _ja Understanding Counterexamples:

反例を理解する
-----------------------------

ある検査項目が証明されないとき， |GNATprove| が反例を生成する場合があります．反例は，2つの部分から構成されます．

* サブプログラムに対するパス或いはパスの組
* パス上に現れる変数への値の割り当て

反例を見るためにもっとも良い方法は，GPS 上で不合格となった証明メッセージの左にあるアイコンをクリックスすることです．或いは，エディタ上で関連する行の左側をクリックすることです（次を参照： :ref:`ja Running GNATprove from GPS` )． |GNATprove| は，色でパスを表示します．これらの値を表示しているエディタ上で（ファイルではなく）挿入する行によってパス上の変数の値を表示することができます．例えば，手続き ``Counterex`` について考えます．

.. literalinclude:: /gnatprove_by_example/examples/counterex.adb
   :language: ada
   :linenos:

入力パラメータ ``Cond`` が ``True`` であり，入力パラメータ ``I1`` と ``I2`` が大きすぎる値の場合，11行の表明文は不合格となります． |GNATprove| が生成する反例は，GPS では以下のように表示されます．ここで，パス上でハイライト表示される各行の次に，前の行における変数の値を示した行が続きます．

.. image:: /static/counterexample.png
   :width: 800 px
   :alt: Counterexample in GPS

|GNATprove| は，また説明付きで，不合格になった証明に対するメッセージを完成させます．即ち，反例に対して，検査済みの式で変数がどういう値をとるかを付け加えます．ここで，11行目で |GNATprove| は，出力パラメータ  ``R`` の値を示すメッセージを出力します．

.. literalinclude:: /gnatprove_by_example/results/counterex.prove
   :language: none
   :lines: 4

|GNATprove| が生成する反例が，いつもプログラムの適切な実行と対応しているとは限りません．

#. 契約やループ不変条件が不足しているとき，プロパティは，証明不能になります（詳しくは次の節をご覧下さい  :ref:`ja Investigating Unprovable Properties` ）．反例は，不足している契約やループ不変条件を見つけるのに役立つ場合があります．例えば，手続き ``Double_In_Call`` の事後条件は，証明不可能です．なぜならば，その手続きが呼び出す関数 ``Double`` の事後条件（の制約）が弱いからです．また，手続き ``Double_In_Loop`` の事後条件は証明不可能です．なぜならば，その手続き中のループがループ不変条件を持たないからです．

   .. literalinclude:: /gnatprove_by_example/examples/counterex_unprovable.ads
      :language: ada
      :linenos:

   .. literalinclude:: /gnatprove_by_example/examples/counterex_unprovable.adb
      :language: ada
      :linenos:

   両方の場合において， |GNATprove| が生成する反例は，検証器が誤って， ``X`` 入力値が 1 のとき， -3 を出力すると演繹するからです．呼び出される関数に契約が欠落している或いはループ実行時のループ不変条件が不足しているのが原因です．

   .. literalinclude:: /gnatprove_by_example/results/counterex_unprovable.prove
      :language: none

#. 検証器の能力不足により（詳細は次の節を参照下さい :ref:`ja Investigating Prover Shortcomings` ），プロパティが証明できないとき，反例を見ることで，検証器がそのプロパティを証明できなかった理由を知ることができる場合があります．しかし，どうして証明機がプロパティを証明できなかったを説明するに過ぎません．ちなみに，CVC4 検証器を使った時のみ常に反例が生成されます．また，もし CVC4 検証器が選択されなれなくても， ``--no-counterexample`` スイッチによって反例の生成が無効になっていないならば，CVC4 を用いて反例を生成しようと試みます．しかし，CVC4 の証明結果は，この場合含まれません．

#. タイムアウトないしはステップ数に小さな値を用いたとき，検証器は，完全な反例を生成する前に，資源制約に掛かるかもしれません．その場合，生成された反例は，適切な実行に対応していないかもしれません．

#. ``--proof`` スイッチの値が，デフォルト値である ``per_check`` であり，サブプログラムの全てのパスにおいて，反例は変数の値を出力します．適切な実行に対応しているパスだけではありません． ``progressive`` 或いは ``per_path`` を用いて， |GNATprove| を再実行することで，反例における可能な実行パスを分離することができます．
