.. _ja Identifying SPARK Code:

************************
|SPARK| コードを指定する
************************

あるプログラムにおいて，一部が |SPARK| で書かれ（ |SPARK| の参照マニュアルにある規則に従っている），別のところでは完全な Ada 2012 で書かれるときがあります．このとき，プログラムないしはアスペクトにおける  ``SPARK_Mode`` によって，どの部分が  |SPARK| かを指定します（指定がない場合は，完全な Ada プログラムとみなします）．

この節では，pragma と ``SPARK_Mode`` アスペクトについて簡単に説明します．詳細は， :ref:`ja Pragma_SPARK_Mode` を参照下さい．

|GNATprove| は，pragma ないしは ``SPARK_Mode`` アスペクトを用いて， |SPARK| と指定している場所に対してのみ，解析を行うことに注意して下さい．

|SPARK| コードと Ada コードの混在
=================================================

Ada プログラムユニット [#f1]_ ないしは，他の構成要素が，「 |SPARK| 」であるというためには， |SPARK| 参照マニュアルに記述されている形式検証を可能とするために必要な制約に適合している必要があります．逆に，ある Ada プログラムユニットないしは，その構成要素が，「 |SPARK| ではない」のは，上記の要求に適合せず，結果として形式検証が実行できない時です．

Ada ユニットないしは，その構成要素を考えたときに， |SPARK| であるか，そうでないかは，次の2つの原則に従って，細かなレベルで組合わせることができます：

* |SPARK| コードは， |SPARK| 宣言のみを参照すること．しかし，Completion [#f2]_ を必要とする |SPARK| 宣言は，非 |SPARK| のボディ部となる場合がある．

* |SPARK| コードは， |SPARK| コードのみを含むべきである．ただし，含まれた |SPARK| 宣言に対応した非 |SPARK| Completion を含む場合がある．

.. rubric:: Footnotes
.. [#f1] ユニットとは，サブプログラム・パッケージ・タスクユニット・保護ユニット（protected unit）・総称体（generic unit）のいずれか．
.. [#f2] Ada 言語において，主として仕様部宣言に対するボディ部での宣言を指す（単純な例としては，あるパッケージの仕様部でサブプログラムが宣言されたとき，パッケージボディ部において，サブプログラムのボディ記述が必要になる．このボディ記述が Completion である）．ここではとりあえず原語を使用する．

もう少し詳細にいうと， 非 |SPARK| の completion となるえるのは，サブプログラム宣言・パッケージ宣言・タスク型宣言・保護型宣言・プライベート型宣言・プライベート拡張宣言・遅延定数宣言 [#f3]_ です．[厳密に言えば，パッケージのプライベート部分，タスク型，保護型は，上記の規則の目的からすると，completion と考えることができる．詳細については以下で記述します］

.. rubric:: Footnotes
.. [#f3] deferred constant declaration: この宣言は可視部分で行う．値は，プライベート部分で与えることができる．他言語で書かれたコードをインポートするときにも用いることができる．

|SPARK| 宣言に対して，非 |SPARK| の completion が与えられるとき，非 |SPARK| completion が， （ |SPARK| の意味論という点から） |SPARK| 宣言を満足していることを示すのは，ユーザの責務になります．例えば， |SPARK| では，関数呼び出しで副作用を生じてはいけません．ある関数のボディ部が |SPARK| であるならば，種々の言語規則に優先して適用されます．そうでなければ，関数ボディ部が規則に違反していないことを示すのはユーザの責務となります．そのような構成要素（特に pargma による仮定）と同様に，ルールに適合できていないと，一部・あるいは全ての |SPARK| に関連した解析（証明やフロー分析）は，無効になってしまいます．非 |SPARK| による completion が， |SPARK| で書かれた場合と意味的に（動的な意味論の点で）同等の completion 記述であるならば， それは，必要条件を満足しているといえます．

前述の要求に適合する混合プログラムにおいて， |SPARK| の意味論（特に，フロー分析や証明）は，明確に定義されています．この意味論は，100% |SPARK| で書かれたプログラムと同等になります．他の「混合」プログラムにおける意味論については，Ada の参照マニュアルを見て下さい．

パッケージ，タスク型，保護型，上記で示した仕様部と completion の区別は，実際には単純化しています．例えば，パッケージは，4つに分割できます．2つではありません．それは，可視部分，プライベート部分，ボディ部の宣言，そしてボディ部の一連の命令です．あるパッケージにおいて，0 .. 4 の数値 N が与えられた場合，パッケージにおいて，最初の N セクションまでは， |SPARK| であることができます．残りは違います．

例えば，次の組み合わせは典型的なものです．

- パッケージ仕様は， |SPARK| で書かれるが，パッケージボディ部は， |SPARK| ではない．

- パッケージ仕様部の可視部は |SPARK| であるが，プライベート部やボディ部は， |SPARK| ではない．

- パッケージ仕様部は， |SPARK| である．パッケージボディ部も，ほとんどは， |SPARK| である．しかし幾つかのサブプログラムボディ部は， |SPARK| ではない．

- |SPARK| で書かれたパッケージ仕様部がある．しかし，サブプログラムのボディ部は，他の言語からインポートしている．

- パッケージの仕様部は， |SPARK| と非 |SPARK| の混合で宣言されている．後者の宣言は， |SPARK| ではないクライアントユニットにとっては可視であり，使用することができる．

タスク型と保護型も上記のパッケージに似ています．しかし，4つの部分ではなく，3つに分かれます．ボディ部の命令列は含まれていません．

これらのパターンは，アプリケーションプログラムが，プログラムのサブセットに対してのみ形式検証を適用することを意図しています．これにより，形式検証とより伝統的なテストを（検証として）組合わせることができます(詳しくは :ref:`ja Applying SPARK in Practice` を参照のこと).

プロジェクトファイルのセットアップ
====================================

プロジェクトファイルによって，プログラムのどの部分が |SPARK| かを粗くですが知ることができることができます．プロジェクトファイルのセットアップについて詳しく知るためには，次の章を見て下さい． :ref:`ja Setting Up a Project File`.

.. _ja Setting the Default SPARK_Mode:

デフォルトのSPARK_Mode を設定する
------------------------------------------

2 つのデフォルト（の利用の仕方）があります．

#. 構成 pragma 中で，``SPARK_Mode`` に値が設定されていない場合です．このときは，プログラム中で明示的に ``SPARK_Mode => On`` を記述している箇所のみが， |SPARK| となります．サブプログラム中でわずかなユニットのみが |SPARK| である場合，このデフォルトの方法を推奨します．

#. 構成 pragma として， ``SPARK_Mode => On`` を設定している．この場合，明示的に ``SPARK_Mode => Off`` が記述されていない限り，全てのプログラムは， |SPARK| ということになります．ほとんどのプログラムが， |SPARK| で記述されている場合，このモードを推奨します．

構成 pragma として， ``SPARK_Mode => On`` の値を指定する方法を示します．

.. code-block:: ada

  project My_Project is
     package Builder is
        for Global_Configuration_Pragmas use "spark.adc";
     end Builder;
  end My_Project;

ここで， ``spark.adc`` が構成ファイルであり，少なくとも次の行を含んでいるとします．

.. code-block:: ada

  pragma SPARK_Mode (On);

.. _ja Specifying Files To Analyze:

解析するファイルを指定する
---------------------------

デフォルトでは，プログラム中の全てのファイルを， |GNATprove| は解析します．もし，一部のプログラムだけが |SPARK| の場合，解析速度を向上させるために，該当するファイルのみを解析する方法もあります．

形式検証のモードに，様々なプロジェクト属性に対して値を設定することで，解析対象ファイルを適切に指定することができます．

 * ``Source_Dirs``: ソースディクレトリの名前リスト
 * ``Source_Files``: ソースファイルの名前リスト
 * ``Source_List_File``: ソースファイルをリスト化しているファイルの名前

例えば，以下の様になります：

.. code-block:: ada

  project My_Project is

    type Modes is ("Compile", "Analyze");
    Mode : Modes := External ("MODE", "Compile");

    case Mode is
       when "Compile" =>
          for Source_Dirs use (...);
       when "Analyze" =>
          for Source_Dirs use ("dir1", "dir2");
          for Source_Files use ("file1.ads", "file2.ads", "file1.adb", "file2.adb");
    end case;

  end My_Project;

その上で， ``MODE`` 外部変数に対して，次のように値を指定した上で， |GNATprove| を呼び出します::

  gnatprove -P my_project -XMODE=Analyze

.. _ja Excluding Files From Analysis:

解析対象からファイルを除外する
-------------------------------------

``SPARK_Mode => On`` というデフォルト値を使用した場合，解析対象から幾つかのファイルを除かないといけない場合があります（例えば，非 |SPARK| コードを含んでいる，或いは，形式的に解析する必要がないコードを含んでいる場合です）．

形式検証のモードにおいて，様々なプロジェクト属性に対して異なる値を設定することで，解析対象から除外するファイルを適切に指定することができます．

 * ``Excluded_Source_Dirs``: 除外するソースディレクトリ名リスト
 * ``Excluded_Source_Files``: 除外するソースファイル名リスト
 * ``Excluded_Source_List_File``: 除外するソースフィル名をリスト化したファイルの名前

例えば，次のように記述します．

.. code-block:: ada

  project My_Project is
     package Builder is
        for Global_Configuration_Pragmas use "spark.adc";
     end Builder;

    type Modes is ("Compile", "Analyze");
    Mode : Modes := External ("MODE", "Compile");

    case Mode is
       when "Compile" =>
          null;
       when "Analyze" =>
          for Excluded_Source_Files use ("file1.ads", "file1.adb", "file2.adb");
    end case;

  end My_Project;

次に, ``MODE`` の値を外部変数として指定した上で， |GNATprove| を呼び出します::

  gnatprove -P my_project -XMODE=Analyze

複数プロジェクトを利用する
----------------------------------

デフォルトを ``SPARK_Mode => On`` とした上で，一部のソースファイルでは， ``SPARK_Mode`` を設定しないで解析すると，便利な場合があります．この場合，異なったデフォルト値を持つ 2 つのプロジェクトファイルを利用することができます．各ソースファイルは，どちらかのプロジェクトファイルのみに属するようにします．そうしても，あるプロジェクトのファイルは，他のプロジェクトのファイルを，プロジェクト間の制限的利用を示す ``limited with`` 節を用いて参照することができます．次のようになります．

.. code-block:: ada

  limited with "project_b"
  project My_Project_A is
     package Compiler is
        for Local_Configuration_Pragmas use "spark.adc";
     end Compiler;
     for Source_Files use ("file1.ads", "file2.ads", "file1.adb", "file2.adb");
  end My_Project_A;

.. code-block:: ada

  limited with "project_a"
  project My_Project_B is
     for Source_Files use ("file3.ads", "file4.ads", "file3.adb", "file4.adb");
  end My_Project_B;

ここで， ``spark.adc`` は，少なくとも次の行を含んでいる構成ファイルです．

.. code-block:: ada

  pragma SPARK_Mode (On);

.. _ja Using SPARK_Mode in Code:

コード中で ``SPARK_Mode`` を用いる
=================================================

プログラム中のどの部分が |SPARK| であるかを細かく指定するために，pragma ないしは ``SPARK_Mode`` アスペクトを用いることができます．

基本的な使い方
-----------------------

SPARK_Mode pragma は，次のように指定します．

.. code-block:: ada

   pragma SPARK_Mode [ (On | Off) ]

例えば：

.. code-block:: ada

   pragma SPARK_Mode (On);
   package P is

SPARK_Mode アスペクトの場合は，次のようになります：

.. code-block:: ada

   with SPARK_Mode => [ On | Off ]

例えば：

.. code-block:: ada

   package P with
     SPARK_Mode => On
   is

SPARK_Mode pragma ないしはアスペクトは，明示的に引数の指定のないまま用いると，デフォルトでは ON となります．

例えば:

.. code-block:: ada

   package P is
      pragma SPARK_Mode;  -- ここでは暗黙的に ON です

或いは
or

.. code-block:: ada

   package P with
     SPARK_Mode  --  ここでは暗黙的に ON です
   is

パッケージまたはサブプログラムが，トップレベルのパッケージであるか，ライブラリレベルパッケージ中で定義されているとき，ライブラリレベルと呼びます． ``SPARK_Mode`` pragma は，コード中の次の場所で使用することができます．

* ライブラリレベルパッケージ仕様部の先頭または前

* ライブラリレベルパッケージボディ部の先頭

* ライブラリレベルパッケージ仕様部の ``private`` キーワードの直後

* ライブラリレベルパッケージボディ部の ``begin`` キーワードの直後

* ライブラリレベルサブプログラム仕様の直後

* ライブラリレベルサブプログラムボディ部の先頭

* ライブラリレベルタスク仕様部の先頭

* ライブラリレベルタスクボディ部の先頭

* ライブラリタスク仕様部の ``private`` キーワードの直後

* ライブラリレベル保護仕様部の先頭

* ライブラリレベル保護ボディ部の先頭

* ライブラリレベル保護仕様部の ``private`` キーワードの直後

``SPARK_Mode`` アスペクトは，コード中の以下の場所で利用可能です．

* ライブラリレベルのパッケージ仕様部あるいはボディ部

* ライブラリレベルのサブプログラム仕様部あるいはボディ部

* ライブラリレベルのタスク仕様部あるいはボディ部

* ライブラリレベルの保護仕様部あるいはボディ部

もし，サブプログラム・パッケージ・タスク・保護領域の仕様部／ボディ部で ``SPARK_Mode`` pragma ないしはアスペクトが指定されていない場合，宣言がある場所において有効な現在のモードを継承します．

一貫性規則
------------

いったん， ``SPARK_Mode`` をオフにしたら，再度オンにはできない，というのが基本的な規則です．従って，次のルールが適用されます：

もし，あるサブプログラム仕様が， ``SPARK_Mode`` をオフにしたならば，ボディ部は， ``SPARK_Mode`` をオンにすることはできない．

パッケージには，4つの部分があります．

#. パッケージの公開宣言
#. パッケージのプライベート部分
#. パッケージのボディ部
#. ``begin`` に続く，実行時準備処理(elaboration) [#f4]_ コード

.. rubric:: Footnotes
.. [#f4] Ada言語においては，宣言がランタイム中に与える影響を処理する過程のこと．

パッケージに関しては次のようになります．任意の箇所で明示的に ``SPARK_Mode`` をオフにしたときは，以降の場所では， ``SPARK_Mode`` をオンにすることができません．このとき，ボディ部において，再度 ``SPARK_Mode(Off)`` を必要とする場合もあることに注意して下さい．例えば，構成 pragma に，デフォルトとしてモードをオンにする ``SPARK_Mode (On)`` があるとします．あるパッケージの仕様部で， ``SPARK_Mode (Off)`` にしたとします．このとき，この pragma を，ボディ部で繰り返す必要があります．

タスク型と保護型も同様です．もし， ``SPARK_Mode`` が以下のある箇所でオフに設定されたならば，引き続く他の場所ではオンにすることはできません．

#. 仕様部
#. プライベート領域
#. ボディ部

このルールには例外があります． ``SPARK_Mode`` がオフである汎用体をインスタンス化したコードにおいて，汎用体中の ``SPARK_Mode`` の値は，このインスタンスでは無視されます．

利用例
---------------

.. _ja Verifying Selected Subprograms:

選択したサブプログラムを検証する
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

もし，限られたわずかなサブプログラムが |SPARK| であり， ``SPARK_Mode`` をデフォルトでオンにすることに意味がないのならば，``SPARK_Mode => On`` にする代わりに，該当するサブプログラムに対して，直接オンの指定を行います．例えば：

.. literalinclude:: /gnatprove_by_example/examples/selected_subprograms.ads
   :language: ada
   :linenos:

[注］ ``Sub_Action`` と ``Non_Critical_Action`` 手続きボディ部は解析されませんが，手続き ``Critical_Action`` のボディ部で ``Sub_Action`` を呼び出すことは正しいことです．このとき， ``Sub_Action`` の仕様部において， ``SPARK_Mode
=> On`` とする必要はありません．実際， |GNATprove| は， ``Sub_Action`` の仕様部が， |SPARK| であるとして検査します．

.. literalinclude:: /gnatprove_by_example/examples/selected_subprograms.adb
   :language: ada
   :linenos:

.. _ja Verifying Selected Units:

選択したユニットを検証する
^^^^^^^^^^^^^^^^^^^^^^^^^^^

もし，ある限られたわずかなユニットが |SPARK| であり， ``SPARK_Mode`` をデフォルトでオフにすることに意味があるのならば，``SPARK_Mode => On`` にする代わりに，該当するユニットに対して，直接オンの指定を行います．例えば，

.. literalinclude:: /gnatprove_by_example/examples/selected_units.ads
   :language: ada
   :linenos:

[注] ``Sub_Action`` を， |SPARK| コード中で呼び出すことができます．なぜならば，ボディ部には，``SPARK_Mode => Off`` とマークされていますが，その仕様部は |SPARK| だからです．逆に，仕様部が，``SPARK_Mode => Off`` とマークされている ``Non_Critical_Action`` 手続きは， |SPARK| コード中で，呼び出すことができません．

.. literalinclude:: /gnatprove_by_example/examples/selected_units.adb
   :language: ada
   :linenos:

.. _ja Excluding Selected Unit Bodies:

選択したユニットボディ部を除く
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

もし，あるユニットの仕様部が |SPARK| であり，ボディ部が |SPARK| ではない場合，仕様部は， ``SPARK_Mode => On`` とマークされ，ボディ部は， ``SPARK_Mode => Off`` とマークされます．こうすることで，クライアントコードが，このユニットを使用するときに， |SPARK| であることができます．もし，デフォルトで ``SPARK_Mode`` がオンであれば，ユニットの仕様部でオンの指定を繰り返す必要はありません．

.. literalinclude:: /gnatprove_by_example/examples/exclude_unit_body.ads
   :language: ada
   :linenos:

仕様部のプライベート領域（物理的には仕様部ファイル中に存在することになりますが，論理的にはボディ部と同等になります）は， ``SPARK_Mode (Off)`` pragma をプライベート領域の最初に指定することで，同様に除外することができます．

.. literalinclude:: /gnatprove_by_example/examples/exclude_unit_body.adb
   :language: ada
   :linenos:

この方式は，汎用体（generic）ユニットにおいても同様に機能します．次の場合にも成立します：``SPARK_Mode`` がオンである場合，インスタンス化された汎用体のボディ部のみを除外する． ``SPARK_Mode`` がオフである場合，インスタンス化された汎用体の仕様部とボディ部を除外することができます．

.. literalinclude:: /gnatprove_by_example/examples/exclude_generic_unit_body.ads
   :language: ada
   :linenos:

.. literalinclude:: /gnatprove_by_example/examples/exclude_generic_unit_body.adb
   :language: ada
   :linenos:

.. literalinclude:: /gnatprove_by_example/examples/use_generic.ads
   :language: ada
   :linenos:

.. literalinclude:: /gnatprove_by_example/examples/use_generic.adb
   :language: ada
   :linenos:

.. _ja Excluding Selected Parts of a Unit:

ユニットの選択した領域を取り除く
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

特定のサブプログラムとパッケージを除くほとんどのユニットが |SPARK| であるならば， ``SPARK_Mode (On)`` を設定することは合理的です．その上で， ``SPARK_Mode => Off`` を，非 |SPARK| 宣言に対して設定します．ここでは， ``SPARK_Mode => On`` を構成 pragma として指定することを考えます．

.. literalinclude:: /gnatprove_by_example/examples/exclude_selected_parts.ads
   :language: ada
   :linenos:

手続き ``Non_Critical_Action`` が， |SPARK| コード中で呼ばれる場合があることに注意して下さい．ボディ部は， ``SPARK_Mode => Off`` とマークされていますが，仕様部は， |SPARK| コードだからです．

局所的パッケージ ``Non_Critical_Data`` は， ``SPARK_Mode => Off`` とマークされているので，非 |SPARK| 型，変数，サブプログラムを含むことができます．非 |SPARK| 宣言を集めたこういったパッケージを定義すると便利かもしれません．そうしておけば，ユニット ``Exclude_Selected_Parts`` を ``SPARK_Mode => On`` としておくことができます．

.. literalinclude:: /gnatprove_by_example/examples/exclude_selected_parts.adb
   :language: ada
   :linenos:
