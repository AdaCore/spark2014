[![CII Best Practices](https://bestpractices.coreinfrastructure.org/projects/959/badge)](https://bestpractices.coreinfrastructure.org/projects/959)

# 1. Introduction

This repository contains the source code for the SPARK 2014 project. SPARK
is a software development technology specifically designed for engineering
high-reliability applications. It consists of a programming language,
a verification toolset and a design method which, taken together, ensure
that ultra-low defect software can be deployed in application domains where
high-reliability must be assured and where safety and security are
key requirements.

This repository provides visibility on the development process. The main line
of development is in line with the development version of GNAT, which is not
directly visible to the public (although patches are regularly transferred to
the FSF repository at ``svn://gcc.gnu.org/svn/gcc/trunk/gcc/ada``), and it will
probably be impossible to build the master branch of the software with any
other compiler. However, buildable branches are provided corresponding to
public compiler releases or the head of the FSF repository, see the section on
*Building SPARK* below.

# 2. Commercial support

SPARK is commercially supported by AdaCore and Altran, you can visit the
[AdaCore website](http://www.adacore.com/sparkpro/) for more information.

# 3. Community version

There is a Community version of the tools, readily packaged, and suitable for
research and hobbyist use. You can download it from
[AdaCore's website](https://www.adacore.com/download).

# 4. Community

News about SPARK project are shared primarily on [AdaCore's
blog](https://blog.adacore.com/). Discussions about SPARK occur on [a public
mailing-list](https://lists.adacore.com/mailman/listinfo/spark2014-discuss).

# 5. Documentation

You can find the definition of the SPARK language in the
[SPARK Reference Manual](https://docs.adacore.com/live/wave/spark2014/html/spark2014_rm/index.html),
and instructions on how to use the tool, together with a tutorial, in the
[SPARK User's Guide](https://docs.adacore.com/live/wave/spark2014/html/spark2014_ug/index.html).

# 6. Building SPARK

In order to build SPARK, you need to first install the following dependencies
(and we recommend using the OPAM package manager for these):

* ocaml compiler
* ocamlgraph library
* menhir parser
* zarith library
* camlzip library
* ocplib-simplex library

SPARK sources are tied to the sources of GNAT compiler frontend. For this
reason, you should use a compiler built from sources with a date matching the
sources of SPARK. There are two options.

## 6.1 Building SPARK with GNAT Community

To build SPARK with GNAT Community compiler, you need to use the corresponding
branch of this repository. For example, to build with GNAT Community 2020, use
the branch gpl-2020, as follows:

```
git checkout gpl-2020
```

SPARK repository uses submodules to keep in sync with corresponding versions
of Why3, Alt-Ergo, CVC4 and Z3, which generally track the main repositories for
these tools with minor modifications for the integration with SPARK. To
retrieve the corresponding branch of these submodules, do:

```
git submodule init
git submodule update
```

Then follow the instructions in the [Makefile](https://github.com/AdaCore/spark2014/blob/master/Makefile).

## 6.2 Building SPARK with GNAT FSF

To build SPARK with GNAT version from FSF, you need to use the corresponding
branch of this repository which follows the latest changes pushed at FSF, as
follows:

```
git checkout fsf
```

To retrieve the most recent version of the submodules for Why3, Alt-Ergo, CVC4
and Z3, which matches the latest changes for SPARK pushed at FSF, do:

```
git submodule init
git submodule update
```

Then follow the instructions in the [Makefile](https://github.com/AdaCore/spark2014/blob/master/Makefile).
