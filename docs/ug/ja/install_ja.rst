.. _ja Installation of GNATprove:

|GNATprove| をインストールする
=====================================

最初に，GPS（および任意で GNAT）をインストールすることをおすすめします．次に，同じ場所に， |GNATprove| をインストールします．GPS を用いないで，Eclipse　用の GNATbench プラグインをインストールすることもできます．このインストールには，Eclipse の一般的なインストール方法を利用します．

|GNATprove| を別の場所にインストールする場合は， ``GPR_PROJECT_PATH`` 環境変数を変更する必要があります（GNATをインストールしたならば）．ウィンドウズの場合は，環境変数パネル中で ``GPR_PROJECT_PATH`` を追加し，次のパスを設定します： ``<GNAT install dir>/share/gpr``  および，``<GNAT install dir>/share/gpr`` ．これによって， |SPARK| は，GNAT とともにインストールしたライブラリプロジェクトを見つけることができるようになります．また， ``<SPARK install dir>/lib/gnat`` を追加します．これによって，GNATは，SPARK とともにインストールされた補題ライブラリプロジェクト を見つけることができるようになります．Linux/Mac で Bourne シェルを使用している場合は，以下を設定して下さい．
::

  export GPR_PROJECT_PATH=<GNAT install dir>/lib/gnat:<GNAT install dir>/share/gpr:<SPARK install dir>/lib/gnat:$GPR_PROJECT_PATH

Linux/Mac で Cシェルの場合は以下です::

  setenv GPR_PROJECT_PATH <GNAT install dir>/lib/gnat:<GNAT install dir>/share/gpr:<SPARK install dir>/lib/gnat:$GPR_PROJECT_PATH

GPS と |GNATprove| の詳細なインストール手順については，以下を参照下さい．

Windowsへのインストール
--------------------------

まだであれば，最初に GPS インストーラを実行します．例えば，`gps-6.0.2-i686-pc-mingw32.exe`  をダブルクリックし，指示に従います．

.. note::

  もし，GNAT Pro ではなく，GNAT GPL を使用する場合，GNAT GPL インストーラをお使い下さい．そうすれば，GPS がインストールされます．

同様に， |GNATprove| をインストーラを実行して下さい．例えば，`spark-15.0.2-x86-windows-bin.exe` をダブルクリックします．

パッケージをインストールするために，十分な権限を持っている必要があります（管理者権限か一般ユーザ権限かです．これは，全てのユーザ用にインストールしたいか，シングルユーザ用にインストールするかによって決まります）．

Linux/Mac にインストールする
----------------------------

まだであれば，GPS の tar 圧縮ファイルを展開し，インストールします．例えば，::

  $ gzip -dc gps-6.0.2-x86_64-linux-bin.tar.gz | tar xf -
  $ cd gps-6.0.2-x86_64-linux-bin
  $ ./doinstall

次に，表示される指示に従います．

.. note::

  もし，もし，GNAT Pro ではなく，GNAT GPL を使用する場合，GNAT GPL インストーラをお使い下さい．そうすれば，GPS がインストールされます．

次に，SPARK tar 圧縮ファイルに対して，同様のことをして下さい．例えば．::

  $ gzip -dc spark-15.0.2-x86_64-linux-bin.tar.gz | tar xf -
  $ cd spark-15.0.2-x86_64-linux-bin
  $ ./doinstall

指定した場所にパッケージをインストールために，十分な権限を持っている必要があります（例えば，/opt/spark以下にインストールするためには，ルート権限が必要です）．
