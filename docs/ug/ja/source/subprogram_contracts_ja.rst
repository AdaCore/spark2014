.. _ja Subprogram Contracts:

サブプログラム契約
====================

|SPARK| プログラムの振る舞いの意図を記述するために，最も重要な特徴は，サブプログラムに「契約」を加えることができることです．ここでは，`subprogram` は手続き，関数，保護エントリを指します．この契約は，様々な付加的な構成品を用いて作成します．

* 事前条件 `precondition` では，サブプログラムを呼び出すときに呼び手が守るべき制約を，アスペクト ``Pre`` によって示します．
* 事後条件 `postcondition` では，サブプログラムの機能的振る舞いを，アスペクト ``Post`` によって（部分的にないしは全て）規定します．
* 契約ケース `contract cases` では，サブプログラムの振る舞いを分割するために，アスペクト ``Contract_Cases`` を用います．これは，事前条件・事後条件を補ったり，置き換えることができます．
* データ依存では，アスペクト ``Global`` を用いて，サブプログラムによって読み書きさえる広域データを特定します．
* フロー依存では，アスペクト ``Depends`` を用いて，サブプログラム出力がどのようにサブプログラム入力に依存しているかを識別します．

サブプログラムにおける契約は，呼び出しが成功するためのふるまいを規定します．エラーの送出により終了する実行は， :ref:`ja Raising Exceptions and Other Error Signaling Mechanisms` に記述しているように，サブプログラム契約では，カバーすることができません．実行が正常に終了する場合，あるいは．何らかの出力を持つアスペクト ``No_Return`` がマークされているサブプログラムに対して，エラーなしに実行がループするならば，サブプログラム呼び出しは成功です（制御器のメインループのサブプログラムを非終了サブプログラムとして実装することは典型的なケースとなります）．

.. _ja Preconditions:

事前条件
-------------

[Ada 2012]

サブプログラムの事前条件とは，そのサブプログラムを呼び出すコードに制約を加えることです．通常，事前条件は，制約の論理積として記述することができます．なお，各制約は以下のカテゴリのいずれかになります．

* 禁止された値をパラメータから除外．例えば， ``X /= 0`` 或いは ``Y not in Active_States``
* 取り得るパラメータ値の仕様．例えば， ``X in 1 .. 10`` 或いは ``Y in Idle_States``
* パラメータ間で維持すべき値の関係．例えば， ``(if Y in Active_State then Z /= Null_State)``
* 計算途中の状態を表現する広域変数の期待値．例えば， ``Current_State in Active_States``
* サブプログラムを呼び出すきに，維持すべき広域状態に関する不変条件．例えば， ``Is_Complete (State_Mapping)``
* サブプログラムを呼び出すときに，維持すべき広域状態と入力パラメータの関係．例えば， ``X in Next_States (Global_Map, Y)``

プログラムが，表明とともにコンパイルされるとき（例えば， |GNAT Pro| において ``-gnata`` スイッチとともに），サブプログラムの事前条件は，実行中サブプログラムが呼び出される都度検査されます．事前条件が成立しない場合，例外を送出します．全ての表明で，このことが必要なわけではありません．例えば，共通のイディオムとしては，次のように pragma  ``Assertion_Policy`` を設定することで，バイナリ中で事前条件のみを検査可能にします（他の表明は検査しません）．

.. code-block:: ada

   pragma Assertion_Policy (Pre => Check);

サブプログラムを， |GNATprove| で解析するとき，実行するコンテキストに限定して事前条件を用います．これは，サブプログラムの実装が以下であることを証明するために，一般に必要なことです．

* サブプログラムには実行時エラーがない
* サブプログラムの事後条件が常に維持されていることを保証する

特に，デフォルトの事前条件 ``True`` を，明示的な事前条件が存在しない場合に |GNATprove| が用います．しかし， |GNATprove| によって呼び手のコンテキストを解析することができない時，正確ではない可能性があります． |GNATprove| が呼び手を解析する時，呼び出し時点で保持している呼び出されるサブプログラムの事前条件を検査します．そして， |GNATprove| によって，サブプログラムの実装が解析されないときでも，呼び出しているコードを解析するために，サブプログラムに対して事前条件を付け加えることは必要です．

例えば， ``Add_To_Total`` 手続きを考えます．これは，パラメータ ``Incr`` が持つ値によって，広域カウンタである ``Total`` の値を増やします．実装において，整数のオーバーフローが発生しないことを保証するために， ``Incr`` は大き過ぎる値をとることはできません．これは，次のような事前条件で示すことができます．

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Pre => Incr >= 0 and then Total <= Integer'Last - Incr;

``Total`` の値が，非負であることを保証するために，次の条件 ``Total >= 0`` を事前条件に加えることもできます．

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Pre => Incr >= 0 and then Total in 0 .. Integer'Last - Incr;

全てのコンテキストで，実行時エラーがないことを保証するために， |GNATprove| は，事前条件を解析します．このために，特別な事前条件の書き方が必要になります．例えば，前述の ``Add_To_Total`` の事前条件は，短いブール演算子である ``and then`` を， ``and`` の代わりに用いています．手続きを呼び出したときに， ``Incr`` が負であることを確認しているので， ``Integer'Last - Incr``がオーバフローすることはありません．別の言い方をすると， ``and then`` の利用により，式 ``Integer'Last - Incr`` が評価される前に，事前条件の非成立を確認できるということになります．

.. note::

   事前条件中で， ``and`` の代わりに短いブール演算子である ``and then`` を使用するのは，よい習慣です．事前条件中で， |GNATprove| が実行時エラーがないことを証明するために，必要な場合があります．

.. _ja Postconditions:

事後条件
--------------

[Ada 2012]

サブプログラムの事後条件には，部分的，或いは完全なサブプログラムの機能的振る舞いを記述します．通常，事後条件は，次のカテゴリのいずれかの特性の論理積として書くことができます．

* 取り得る関数の返値．特別の属性 ``Result`` を使用します．次が例です： ``Get'Result in Active_States``
* 出力パラメータの取り得る値．例えば， ``Y in Active_States``
* 出力パラメータ間の期待する関係．例えば，  ``if Success then Y /= Null_State``
* 入力と出力パラメータ間の期待する関係．特別な属性である ``Old`` を用います．例えば， ``if Success then Y /= Y'Old``
* 計算状態の更新を示す広域変数の期待する値．例えば， ``Current_State in Active_States``
* サブプログラムからの戻りで保持すべき広域変数の不変条件．例えば，  ``Is_Complete (State_Mapping)``
* 広域状態とサブプログラムからの戻りで保持すべき出力パラメータとの間にある関係．例えば， ``X in Next_States (Global_Map, Y)``

プログラムを表明とともにコンパイルするとき（例えば |GNAT Pro| であれば ``-gnata`` スイッチを使用する），サブプログラムの事後条件は，実行中にサブプログラムから戻るときは常に検査されます．事後条件が不成立だった場合，例外が送出されます．通常，事後条件はテスト中有効です．事後条件は，プログラムが意図したとおり振る舞っていることを確認する動的で検査可能な答え（oracle）を提供しているからです．最終的にバイナリを作るときは，効率化のために動作しないようにすることができます．

サブプログラムを， |GNATprove| で解析する時，サブプログラムの事後条件が不成立とならないということを検査します．この検証は，モジュール化されています： |GNATprove| は，サブプログラムの事前条件が持っている全ての呼び出しコンテキストを考慮します． |GNATprove| は，また，事後条件は実行時エラーを生じないということを保証するために，他の表明と同様の解析を行います．

例えば，手続き ``Add_To_Total`` を考えます．これは，パラメータ ``Incr`` が持つ値によって，広域カウンタである ``Total`` を増加します．この意図した振る舞いは，事後条件として次のように書くことができます．

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Post => Total = Total'Old + Incr;

サブプログラムの事後条件は，そのサブプログラムの呼び出しを解析するために用います．特に，明示的な事後条件がないとき， |GNATprove| が使用するデフォルトの事後条件 ``True`` は，呼び手の特性を証明するために十分に正確ではないかもしれません．サブプログラムが呼び手のコンテキストで実装されていないときは，そうなります．

再帰的サブプログラムや相互に再帰的なサブプログラムは，ここでは，明示的に非再帰的サブプログラムとして扱います．これらサブプログラムは，常に終了します（特性は， |GNATprove| によって，検証されません）． |GNATprove| は各再帰呼び出し時の事後条件を用いることによって，事後条件に違反がないことを検査します．

ブール値を返す関数に対しては，特別な注意が必要です．よくある誤りは，事後条件として，期待するブール値結果を書いてしまうことです．　　　　　　　　

.. code-block:: ada

   function Total_Above_Threshold (Threshold : in Integer) return Boolean with
     Post => Total > Threshold;

正しい事後条件として，次を用います Attribute Result:

.. code-block:: ada

   function Total_Above_Threshold (Threshold : in Integer) return Boolean with
     Post => Total_Above_Threshold'Result = Total > Threshold;

|GNAT Pro| コンパイラと |GNATprove| は，意味的には正しいが，機能的には間違っている可能性のある事後条件に対して警告を発行します．

.. _ja Contract Cases:

契約ケース
--------------

[|SPARK|]

サブプログラムが，異なった機能的振る舞いの決まった組を持っているのであれば，これら振る舞いを事後条件というより契約ケースとして記述するのが便利です．例えば，ある手続きの変種を考えます．手続き ``Add_To_Total`` は，広域カウンタ ``Total`` を，それが可能な場合にパラメータ値を与えることにより増加させるか，ある閾値でそれ以上は大きくならないとします．これら振る舞いは，契約ケースでは次のように定義することが可能です．

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Contract_Cases => (Total + Incr < Threshold  => Total = Total'Old + Incr,
                        Total + Incr >= Threshold => Total = Threshold);

各契約ケースは，ガード中で構成され， 結果は，シンボル ``=>`` により分離されます．サブプログラムへのエントリで，ガートが ``True`` と評価できたとき，サブプログラムの終了時に，対応する対応する条件文は， ``True`` と評価されます．この契約ケースは，呼び出しに対して起動された（enabled）ということができます．正確に一つの契約ケースが，各呼び出しに対して起動されるべきです．或いは，契約ケースは，互いに素であり完備しているべきと言うことができます．

例えば， ``Add_To_Total`` の契約ケースは，サブプログラムは 2 つの異なるケースのみで呼び出されるべきと示しています．

* ``Total`` の値を増加させる入力は，厳密に与えられた閾値より小さくなくてはなりません．この場合，手続き ``Add_To_Total`` は，``Total`` を入力値分増加します．
*  ``Total`` に入力値を加えたときに，閾値を超えるならば，手続き ``Add_To_Total`` は， ``Total`` の値を閾値の値とします．

プログラムを表明とともにコンパイルするとき（例えば， |GNAT Pro| では，``-gnata`` スイッチを用いる），全てのカード条件は，サブプログラムへのエントリ時点で評価されます．正確にどれか一つが ``True`` であることを実行時に検査します．この選択された契約ケースに関して，サブプログラムから戻ってきた時の別の実行時検査があります．それは，サブプログラムから制御が戻ってきた時に，関連する結果が ``True`` と評価できるかの検査です．

サブプログラムを， |GNATprove| とともに解析するとき，契約ケースのうち常に一つだけが有効であり，そのケースは結果として失敗しないことを検査します．もし，サブプログラムが事前条件も持つ場合， |GNATprove| は，事前条件を満足する入力のみ検査します．そうでない場合は，全ての入力をチェックします．

上記に挙げた単純な例において，式の書き方には，等価な事後条件となる複数の書き方があります．特に，次を参照下さい Conditional Expressions:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Post => (if Total'Old + Incr < Threshold  then
                Total = Total'Old + Incr
              else
                Total = Threshold);

   procedure Add_To_Total (Incr : in Integer) with
     Post => Total = (if Total'Old + Incr < Threshold then Total'Old + Incr else Threshold);

   procedure Add_To_Total (Incr : in Integer) with
     Post => Total = Integer'Min (Total'Old + Incr, Threshold);

一般的に，等価な事後条件は，書きづらく・読みづらくなります．契約ケースはまた自動的に検証するための方法を提供しています．これは，入力空間を特定のケースに対応して分割することです．多くのケースがある場合，事後条件中の単純な式を分割することは困難です．

ケースのうちガード条件の最後を  ``others`` とすることができます．これは，それ以前のどのケースにも含まれないあらゆるケースを表しています．例えば， ``Add_To_Total`` の契約は次のように書くことができます：

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Contract_Cases => (Total + Incr < Threshold => Total = Total'Old + Incr,
                        others                   => Total = Threshold);

``others`` をガード条件として用いるとき，検証（実行時や |GNATprove| によるもの）は必要ありません．契約ケースが全ての可能な入力範囲をカバーしているからです．契約ケースが互いに素な場合のみ，検査を行います．

.. _ja Data Dependencies:

データ依存
-----------------

[|SPARK|]

サブプログラムのデータ依存によって，サブプログラムが読み書き可能な広域データを指定します．パラメータに関する記述とともに用いることで，サブプログラムの完全な入力および出力を規定できます．パラメータと同様に，データ依存中で示される広域変数は，入力に対して  ``Input`` モード，出力に対して ``Output`` モード，入力でありかつ出力でもある広域変数に対して ``In_Out`` と記述します．そして，最後に， ``Proof_In`` モードです．これは，契約ないしは表明中でのみ読まれる入力を定義します．例えば，広域カウンタ ``Total`` を増加させる手続き ``Add_To_Total`` のデータ依存は，次のようになります．

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Global => (In_Out => Total);

保護されたサブプログラムでは，保護オブジェクトは，サブプログラムの暗黙的パラメータと考えます：

* 保護関数の暗黙的 ``in`` モードパラメータ
* 保護手続きないしは保護エントリーの暗黙的  ``in out`` モードパラメータ

データ依存は，プログラムのコンパイルや実行時の振る舞いに何の影響も与えません．サブプログラムを |GNATprove| を用いて解析する時，サブプログラムの次の実装を検査します：

* データ依存に指定のある広域入力のみを読み出しいるか
* データ依存に指定のある広域出力のみに書き込んでいるか
* 入力ではない広域出力を常に完全に初期化しているか

|GNATprove| の解析に関するより詳しい内容については， :ref:`ja Data Initialization Policy` を参照のこと．解析中， |GNATprove| は，呼び手を解析するために，呼ばれているコードの記載されたデータ依存を使用します．もし，データ依存が存在しない場合は，呼ばれているコードに対するデフォルトのデータ依存契約が生成されます．

サブプログラム上のデータ依存を記述することにより，様々な利点があります．また，ユーザがデータ依存を契約に追加するのには，様々な理由があります．

* |GNATprove| は，サブプログラムの実装が，広域データへの指定したアクセスを遵守しているかを自動的に検証します．
* |GNATprove| は，サブプログラムの呼び手のデータおよびフロー依存を解析するために，フロー解析を行うときに指定した契約を利用します．これは単に生成されたデータ依存よりも精度の高い（即ち間違った警告が少ない）解析が可能となります．
* |GNATprove| は，実行時エラーがないこと，およびサブプログラムの呼び出し側の機能的な契約を検査するために，証明中に指定した契約を用います．こうすることで，単に生成されたデータ依存を用いるよりもより精度の高い（即ち間違った警告が少ない）解析が可能となります．

データ依存が，サブプログラム上で指定されているとき，サブプログラムにおける全ての広域データの読みだしと，書き込みの全てを指定すべきです．もし，サブプログラムが，広域的入力も出力も持たない場合は， ``null`` データ依存を用いて，記述することができる．

.. code-block:: ada

   function Get (X : T) return Integer with
     Global => null;

サブプログラムが，広域入力のみを持ち，広域出力を持たない場合， ``Input`` モードを用いて規定します：

.. code-block:: ada

   function Get_Sum return Integer with
     Global => (Input => (X, Y, Z));

或いは，モードなしで記載しても同値になります．

.. code-block:: ada

   function Get_Sum return Integer with
     Global => (X, Y, Z);

（注）任意のモードに対する広域入力あるいは広域出力のリストには括弧を用いること．

読み書きされる広域データは，``In_Out`` モードとして記述されるべきです．入力と出力と分けてはいけません．例えば， ``Add_To_Total`` に対するデータ依存の記述は不正であり， |GNATprove| は，エラーとします．

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Global => (Input  => Total,
                Output => Total);  --  INCORRECT

サブプログラム中で，部分的に記載されている広域データも，出力とはせずに ``In_Out`` とすべきです．詳しくは次を参照下さい　 :ref:`ja Data Initialization Policy`.

.. _ja Flow Dependencies:

フロー依存
-----------------

[|SPARK|]

サブプログラムのフロー依存では，サブプログラムの出力（出力パラメータと広域的出力）が入力（入力パラメータと広域入力）に如何に依存しているかを指定します．例えば，広域カウンタ  ``Total`` の値を増加する手続き ``Add_To_Total`` のフロー依存は次のように規定できます：

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Depends => (Total => (Total, Incr));

上記のフロー依存は，次のように読むことができます．「広域変数 ``Total`` の出力値は，広域変数 ``Total`` とパラメータ ``Incr`` に依存している」

保護サブプログラムに関しては，保護オブジェクトをサブプログラムの暗黙的パラメータと考えることができ，保護ユニット（型あるいはオブジェクト）という名前を使って，フロー依存中で次のように宣言可能です．

* 保護関数の暗黙的 ``in`` モードのパラメータとして．フロー依存の右手側に記載します．
* 保護手続き或いは保護エントリの暗黙的 ``in out`` モードパラメータとして． フロー依存の左手側・右手側両方に記載できます．

フロー依存は，プログラムのコンパイルや実行時の振る舞いに何の影響も与えません．サブプログラムが， |GNATprove| で解析されるとき，サブプログラムの実装中で，フロー依存で規定したように，出力が入力に依存していることを検査します．その解析中， |GNATprove| は，呼び手を解析するために，呼ばれるコードに規定されたフロー依存を利用します．もしフロー依存の記述がない場合，呼ばれる側のコードには，デフォルトのフロー依存契約が，生成されます．

フロー依存がサブプログラムにおいて指定された時，入力から出力への全てのフローを記述する必要があります．特に，部分的に書かれているパラメータの出力値或いは広域的変数が，その入力値に依存する場合はそうです．（詳しくは， :ref:`ja Data Initialization Policy` を参照下さい）

パラメータあるいは広域変数の出力値が，その入力値に依存するとき，関係するフロー依存は，短縮シンボル ``*`` を使用することができます．このシンボルによって，変数の出力値は，変数の入力値とリスト化された他の入力に依存しているということ示すことができます．例えば，``Add_To_Total`` のフロー依存は，次のように指定でき，それは同値となります：

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Depends => (Total =>+ Incr);

出力値が入力値に依存しないときは，出力値は定数によって（再）初期化されているだけなので入力値には依存しないということを意味し，そのことを示すフロー依存では， ``null`` 入力リストを用いることができます：

.. code-block:: ada

   procedure Init_Total with
     Depends => (Total => null);

.. _ja State Abstraction and Contracts:

状態抽象と契約
-------------------------------

[|SPARK|]

これまでに説明してきたサブプログラム契約では，直接に広域変数を扱ってきました．多くの場合そうすることができません．広域変数は，他のユニットで定義されていたり，直接見ることができないからです（パッケージ仕様のプライベート領域で定義されているか，パッケージ実装いおいて定義されているからです）．その場合は， 契約における不可視の広域データを示すために，|SPARK| における抽象状態の表記を用いることができます．

.. _ja State Abstraction and Dependencies:

状態抽象と依存
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

もし，手続き ``Add_To_Total`` によって値を増加する広域変数 ``Total`` がパッケージの実装で定義され，クライアントパッケージ中の手続き ``Cash_Tickets`` が， ``Add_To_Total`` を呼び出しているとします． ``Total`` を定義しているパッケージ ``Account`` は， ``Total`` を示す抽象状態 ``State`` を定義することができます． それを，``Cash_Tickets`` のデータ・フロー依存中で，用いることができます．

.. code-block:: ada

   procedure Cash_Tickets (Tickets : Ticket_Array) with
     Global  => (Output => Account.State),
     Depends => (Account.State => Tickets);

広域変数 ``Total`` は，ユニット ``Account`` のクライアントからは不可視になるので， ``Account`` の仕様部の可視領域においても不可視になります．それ故， ``Account`` における外部から可視のサブプログラムは，そのデータ・フロー依存中で，抽象状態 ``State`` を使う必要があります．例えば：

.. code-block:: ada

   procedure Init_Total with
     Global  => (Output => State),
     Depends => (State => null);

   procedure Add_To_Total (Incr : in Integer) with
     Global  => (In_Out => State),
     Depends => (State =>+ Incr);

次に， ``Init_Total`` と ``Add_To_Total`` の実装は，それぞれ ``Refined_Global`` と ``Refined_Depends`` によって導入した洗練したデータおよびフロー依存を定義することができます．この手続き中で，具体的な変数により，サブプログラムに対する正確な依存関係を与えます．

.. code-block:: ada

   procedure Init_Total with
     Refined_Global  => (Output => Total),
     Refined_Depends => (Total => null)
   is
   begin
      Total := 0;
   end Init_Total;

   procedure Add_To_Total (Incr : in Integer) with
     Refined_Global  => (In_Out => Total),
     Refined_Depends => (Total =>+ Incr)
   is
   begin
      Total := Total + Incr;
   end Add_To_Total;

ここで，洗練された依存性は， ``State`` を ``Total`` によって置き換えたときの抽象的依存と同様です．しかし，常にそうとは限りません．特に抽象状態が複数の具体的な変数に置き換えられた場合は，異なります． |GNATprove| は次をチェックします．

* 各抽象広域 input が，具体的広域入力が示している，少なくとも一つの構成物を持っていること．
* 各抽象広域 in_out が，入力モードで指定す構成物の少なくとも一つを持っており，出力モードの一つ（或いは，in_out モードの少なくとも一つの構成物）を持っていること．
* 各抽象広域 output が，具体的広域出力によって示される全ての構成物を持っていること．
* 具体的フロー依存が，抽象フロー依存のサブセットであること．

|GNATprove| は，パッケージ ``Account`` の外部への呼び出しを解析する時， ``Init_Total`` と ``Add_To_Total`` の抽象契約（データとフロー依存）を用います．また，パッケージ ``Account`` の内部への呼び出しを解析する時 ``Init_Total`` と ``Add_To_Total`` のより正確で洗練した契約（即ち洗練したデータとフロー依存）を用います．

洗練した依存は，現在のユニット中で洗練された抽象状態を含んでいるデータと／またはフロー依存のサブプログラムおよびタスクの両方において指定することができます．

.. _ja State Abstraction and Functional Contracts:

状態抽象と関数契約
^^^^^^^^^^^^^^^^^^^^^

もし，グローバル変数が，データ依存に対して可視状態にないとき，関数契約に対しても不可視ということになります．例えば，手続き ``Add_To_Total`` において，広域変数 ``Total`` が可視状態にない場合，関数 ``Add_To_Total`` において， :ref:`ja Preconditions` および :ref:`ja Postconditions` を表現することはできません．その代わり，表現する必要のある状態についてのプロパティを引き出すためのアクセッサとしての関数を定義し，契約に関して利用します．例えば：

.. code-block:: ada

   function Get_Total return Integer;

   procedure Add_To_Total (Incr : in Integer) with
     Pre  => Incr >= 0 and then Get_Total in 0 .. Integer'Last - Incr,
     Post => Get_Total = Get_Total'Old + Incr;

関数 ``Get_Total`` は，パッケージ ``Account`` のプライベート領域ないしは，実装として定義できます．また，通常の関数或いは関数式 の形式となります．例えば：

.. code-block:: ada

   Total : Integer;

   function Get_Total return Integer is (Total);

``Add_To_Total`` の実装に関して，洗練した事前条件や事後条件は必要としませんが， ``Refined_Post`` による洗練された事後条件を与えることは可能です．そして，より正確なサブプログラムの機能的振る舞いにを規定することができます．例えば，手続き ``Add_To_Total`` は，呼び出し毎に ``Call_Count``  カウンタの値を増加させることができ，洗練した事後条件中で表現することができます．

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Refined_Post => Total = Total'Old + Incr and Call_Count = Call_Count'Old + 1
   is
      ...
   end Add_To_Total;

洗練した事後条件は，ユニットが状態抽象を用いないときでさえ，或いは，サブプログラム宣言上で暗黙的に ``True`` 事後条件が用いられているときですら，サブプログラムの実装に与えることができます．

|GNATprove| は，パッケージ ``Account`` の外側で呼び出しを解析するとき，``Add_To_Total`` の抽象契約（事前条件と事後条件）を用います．また， ``Account`` パッケージの内側で呼び出しを解析する時に，``Add_To_Total`` のより正確な洗練した契約（事前条件と事後条件）を用いることができます．
