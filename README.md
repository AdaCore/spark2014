# 1. Introduction

This repository contains the source code for the SPARK 2014 project. SPARK
is a software development technology specifically designed for engineering
high-reliability applications. It consists of a programming language,
a verification toolset and a design method which, taken together, ensure
that ultra-low defect software can be deployed in application domains where
high-reliability must be assured, for example where safety and security are
key requirements.

This repository provides visibility on the development process. The main line
of development is in line with the development version of GNAT, which is not
directly visible to the public (although patches are regularly transfered to
the FSF repository at ``svn://gcc.gnu.org/svn/gcc/trunk/gcc/ada``), and it will
probably be impossible to build the master branch of the software with any
other compiler. However, buildable branches are provided corresponding to
public compiler releases, see the section on *Building SPARK with a GNAT GPL
compiler* below.

# 2. Commercial support

SPARK is commercially supported by AdaCore and Altran, you can visit the
[AdaCore website](http://www.adacore.com/sparkpro/) for more information.

# 3. GPL version

There is a GPL version of the tools, readily packaged, and suitable for
research and hobbyist use. You can download it from
[libre.adacore.com](http://libre.adacore.com/download/).

# 4. Community

News about SPARK project are shared primarily on [a dedicated
blog](http://www.spark-2014.org/). Discussions about SPARK occur on [a public
mailing-list](https://lists.forge.open-do.org/mailman/listinfo/spark2014-discuss).

# 5. Documentation

You can find the definition of the SPARK language in the
[SPARK Reference Manual](http://docs.adacore.com/spark2014-docs/html/lrm/),
and instructions on how to use the tool, together with a tutorial, in the
[SPARK User's Guide](http://docs.adacore.com/spark2014-docs/html/ug/).

# 6. Building SPARK with a GNAT GPL compiler

To build SPARK with a GNAT GPL compiler, you need to use the corresponding
branch of this repository. For example, to build with GNAT GPL 2016, use the
branch gpl-2016, as follows:
```
git checkout gpl-2016
```

SPARK repository uses submodules to keep in synch with corresponding versions
of Why3, Alt-Ergo, CVC4 and Z3, which generally track the main repositories for
these tools, with minor modifications for the integration with SPARK. To
retrieve these submodules, do:
```
git checkout gpl-2016
git submodule init
git submodule update
```

In order to build SPARK, you need to install first the following dependencies
(and we recommend using the Opam package manager for these):

* ocaml compiler
* ocamlgraph library
* menhir parser
* zarith library
* camlzip library
* ocplib-simplex library

Then follow the instructions in the Makefile.
