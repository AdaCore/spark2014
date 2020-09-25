.. _Installation of GNATprove:

Installation of |GNATprove|
===========================

In general, you will need to install a recent version of GNAT toolchain
to compile |SPARK| programs. You will need to install
one toolchain for each platform that you target, for example one toolchain for
native compilation on your machine and one toolchain for cross compilation to
an embedded platform.

For analyzing |SPARK| programs, we recommend to first install GNAT Studio and then
install |GNATprove| under the same location. Alternatively, you can install the
GNATbench plug-in for Eclipse instead of GNAT Studio, using the Eclipse installation
mechanism. The same version of GNAT Studio or GNATbench can support both native and
cross compilations, as well as |SPARK| analysis.

.. index:: GPR_PROJECT_PATH; at installation

If you choose to install |GNATprove| in a different location, you should also
modify the environment variables ``GPR_PROJECT_PATH`` (if you installed GNAT).
On Windows, edit the value of ``GPR_PROJECT_PATH`` under the Environnement
Variables panel, and add to it the value of ``<GNAT install dir>/lib/gnat`` and
``<GNAT install dir>/share/gpr`` (so that |SPARK| can find library projects
installed with GNAT) and ``<SPARK install dir>/lib/gnat`` (so that GNAT can
find the SPARK lemma library project installed with |SPARK|, for details see
:ref:`Manual Proof Using SPARK Lemma Library`). On Linux/Mac with Bourne shell,
use::

  export GPR_PROJECT_PATH=<GNAT install dir>/lib/gnat:<GNAT install dir>/share/gpr:<SPARK install dir>/lib/gnat:$GPR_PROJECT_PATH

or on Linux/Mac with C shell::

  setenv GPR_PROJECT_PATH <GNAT install dir>/lib/gnat:<GNAT install dir>/share/gpr:<SPARK install dir>/lib/gnat:$GPR_PROJECT_PATH

See below for detailed installation instructions of GNAT Studio and |GNATprove|.

System Requirements
-------------------

Formal verification is complex and time consuming, so |GNATprove| will benefit
from all the speed (CPU) and memory (RAM) that can be made available. A minimum
of 2 GB of RAM per core is recommended. More complex analyses will require more
memory. A recommended configuration for running |GNATprove| on large systems is
an x86-64 machine running Linux 64bits or Windows 64bits with at least 8 cores
and 16 GB of RAM. Slower machines can be used to analyze small subsystems, but
a minimum of 2.8Ghz CPU and 2 GB of RAM is required.

In addition, if you want to use the integration of |CodePeer| static analysis
in |GNATprove| (switch ``--codepeer=on``) you will need approximately 1 GB of
RAM per 10K SLOC of code. In other words, in order to analyze 300K SLOC of code
with |CodePeer|, you will need a 64bits configuration with at least 30 GB of
RAM. Note that these numbers will vary depending on the complexity of your
code. If your code is very simple, you will need less memory. On the other hand
if your code is very complex, then you will likely need more memory.

Installation under Windows
--------------------------

If not already done, first run the GNAT Studio installer by e.g. double clicking
on `gnatstudio-<version>-i686-pc-mingw32.exe` and follow the instructions.

.. note::

  If you're using GNAT Commnunity instead of GNAT Pro, you should run instead
  the GNAT Commnunity installer, which installs GNAT Studio and SPARK.

Then similarly run the |GNATprove| installer, by e.g. double clicking on
`spark-<version>-x86-windows-bin.exe`. If you intend to install |GNATprove| in
a location where a previous installation of |GNATprove| exists, we recommend
that you uninstall the previous installation first.

You should have sufficient rights for installing the package (administrator
or normal rights depending on whether it is installed for all users or a
single user).

Installation under Linux/Mac
----------------------------

If not already done, you need to extract and install the GNAT Studio compressed
tarball and then run the install, e.g.::

  $ gzip -dc gnatstudio-<version>-<platform>-bin.tar.gz | tar xf -
  $ cd gnatstudio-<version>-<platform>-bin
  $ ./doinstall

Then follow the instructions displayed.

.. note::

  If you're using GNAT Commnunity instead of GNAT Pro, you should install
  instead the GNAT Commnunity package, which installs GNAT Studio and SPARK.

Then do the same with the SPARK tarball, e.g.::

  $ gzip -dc spark-<version>-<platform>-bin.tar.gz | tar xf -
  $ cd spark-<version>-<platform>-bin
  $ ./doinstall

Note that you need to have sufficient rights for installing the package at the
chosen location (e.g. root rights for installing under /opt/spark).
