.. _ja Formal Verification with GNATprove:

************************************
|GNATprove| を用いた形式検証
************************************

|GNATprove| ツールは， ``gnatprove`` と呼ばれる実行イメージとしてパッケージ化されています．一連の |GNAT Pro| ツール中の他のツールと同様に， |GNAT Pro| は，GNAT プロジェクトの構造に基づき， ``.gpr`` として定義されています．

検証中，実行時に解釈を行うのと全く同様に注釈を解釈するということは， |GNATprove| の大きな特徴です．特に，実行時意味論は，実行時検査の検証を含んでいます．この検証は， |GNATprove| によって静的に実行されます． |GNATprove| は，それ自身の期待される振る舞いの仕様およびコードとの関係に対する付加的な検証も行います．

.. toctree::
   :maxdepth: 2
   :numbered: 3

   source/how_to_run_gnatprove_ja
   source/how_to_view_gnatprove_output_ja
   source/how_to_use_gnatprove_in_a_team_ja
   source/how_to_investigate_unproved_checks_ja
