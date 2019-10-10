.. _ja Installation of GNATprove:

|GNATprove| をインストールする
=====================================

一般に， |SPARK| をコンパイルするためには，最新のバージョンの GNAT ツールチェーン（Ada 2012 構文をサポートしているもの）をインストールする必要があります．ターゲットとする各プラットフォーム毎にツールチェーンをインストールする必要があります．例えば，あるツールチェーンは，自分の計算機用のネイティブコンパイルのためであり，別のものは，組み込みプラットフォームのためのクロスコンパイル用となります．

|SPARK| プログラムを解析するために，最初に，GNAT Studio（および任意で GNAT）をインストールし，次に，同じ場所に， |GNATprove| をインストールすることをお勧めします．GNAT Studio を用いないで，Eclipse　用の GNATbench プラグインをインストールすることもできます．このインストールには，Eclipse の一般的なインストール方法を利用します．GNAT Studio あるいは GNATbench の同一バージョンは，ネイティブ環境とクロスコンパイル環境の両方に利用できます． |SPARK| 解析も同様です．

|GNATprove| を別の場所にインストールする場合は， ``GPR_PROJECT_PATH`` 環境変数を変更する必要があります（GNATをインストールしたならば）．ウィンドウズの場合は，環境変数パネル中で ``GPR_PROJECT_PATH`` を追加し，次のパスを設定します： ``<GNAT install dir>/share/gpr``  および，　``<GNAT install dir>/share/gpr`` ．これによって， |SPARK| は，GNAT とともにインストールしたライブラリプロジェクトを見つけることができるようになります．また， ``<SPARK install dir>/lib/gnat`` を追加します．これによって，GNATは，SPARK とともにインストールされた補題ライブラリプロジェクト を見つけることができるようになります．Linux/Mac で Bourne シェルを使用している場合は，以下を設定して下さい．
::

  export GPR_PROJECT_PATH=<GNAT install dir>/lib/gnat:<GNAT install dir>/share/gpr:<SPARK install dir>/lib/gnat:$GPR_PROJECT_PATH

Linux/Mac で Cシェルの場合は以下です::

  setenv GPR_PROJECT_PATH <GNAT install dir>/lib/gnat:<GNAT install dir>/share/gpr:<SPARK install dir>/lib/gnat:$GPR_PROJECT_PATH

GNAT Studio と |GNATprove| の詳細なインストール手順については，以下を参照下さい．

システム要求
-------------------

形式検証は，複雑で時間を要します．利用可能な速度（CPU）と記憶域（RAM)が十分にあればあるほど |GNATprove| によって良いということになります．CPUコアあたり，2GB の RAM が推奨されます．より複雑な解析では，より多くのメモリが必要になります．大きなシステムに関して， |GNATprove| を動作させるための推奨構成は，Linux 64bit ないしは Windows 64bit OSで，少なくとも 8 コアと 16GB の RAM の構成となります．より遅い計算機で，小さなサブシステムを解析することは可能ですが，最低限 2.8Ghz の CPU と 2GB の RAM が必要となります．

さらに，もし， |GNATprove| と |CodePeer| を一緒に用いようとする場合（ |GNATprove| のスイッチは ``--codepeer=on`` ），10K SLOC のコードに対して約 1 GB のメモリが余分に必要になります．もし，300K SLOC を |CodePeer| で解析するとなると，64bitの構成で，少なくとも 30 GB の RAM が必要と云うことになります．もちろん，この値は，コードの複雑さによって変化します．コードが単純であれば，必要なメモリ量は少なくなりますし，とても複雑であれば，より多くのメモリを必要とします．

Windowsへのインストール
--------------------------

まだであれば，最初に GNAT Studio インストーラを実行します．例えば，`gnatstudio-<version>-i686-pc-mingw32.exe`  をダブルクリックし，指示に従います．

.. note::

  もし，GNAT Pro ではなく，GNAT GPL を使用する場合，GNAT GPL インストーラをお使い下さい．そうすれば，GNAT Studio がインストールされます．

同様に， |GNATprove| をインストーラを実行して下さい．例えば，spark-<version>-x86-windows-bin.exe をダブルクリックします．

パッケージをインストールするために，十分な権限を持っている必要があります（管理者権限か一般ユーザ権限かです．これは，全てのユーザ用にインストールしたいか，シングルユーザ用にインストールするかによって決まります）．

Linux/Mac にインストールする
----------------------------

まだであれば，GNAT Studio の tar 圧縮ファイルを展開し，インストールします．例えば，::

  $ gzip -dc gnatstudio-<version>-<platform>-bin.tar.gz | tar xf -
  $ cd gnatstudio-<version>-<platform>-bin
  $ ./doinstall

次に，表示される指示に従います．

.. note::

  もし，もし，GNAT Pro ではなく，GNAT GPL を使用する場合，GNAT GPL インストーラをお使い下さい．そうすれば，GNAT Studio がインストールされます．

次に，SPARK tar 圧縮ファイルに対して，同様のことをして下さい．例えば．::

  $ gzip -dc spark-<version>-<platform>-bin.tar.gz | tar xf -
  $ cd spark-<version>-<platform>-bin
  $ ./doinstall

指定した場所にパッケージをインストールために，十分な権限を持っている必要があります（例えば，/opt/spark 以下にインストールするためには，ルート権限が必要です）．
