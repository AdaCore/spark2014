[![CII Best Practices](https://bestpractices.coreinfrastructure.org/projects/959/badge)](https://bestpractices.coreinfrastructure.org/projects/959)

# 1. Introduction

This repository contains the source code for the SPARK project. SPARK
is a software development technology specifically designed for engineering
high-reliability applications. It consists of a programming language,
a verification toolset and a design method which, taken together, ensure
that ultra-low defect software can be deployed in application domains where
high-reliability must be assured and where safety and security are
key requirements.

This repository provides visibility on the development process. The main line
of development is in line with the development version of GNAT, which is not
directly visible to the public (although patches are regularly transferred to
the [FSF repository](https://gcc.gnu.org/git/?p=gcc.git;a=tree)), and it will
probably be impossible to build the master branch of the software with any
other compiler. However, buildable branches are provided corresponding to
public compiler releases or the head of the FSF repository, see the section on
*Building SPARK* below.

# 2. Commercial support

SPARK is commercially supported by AdaCore and Capgemini, you can visit the
[AdaCore website](http://www.adacore.com/sparkpro/) for more information.

# 3. Community version

## 3.1 Manual install

You can download a "gnatprove" package from this [github
project](https://github.com/alire-project/GNAT-FSF-builds/releases). Extracting
the package and adding the `bin` directory to your PATH is enough. You can get
the GNAT compiler from the same link, and there is a [different
project](https://github.com/AdaCore/gnatstudio/releases) for GNATStudio, the
IDE.

## 3.2 Install using alire

You can obtain SPARK via [Alire](https://alire.ada.dev/crates/gnatprove). To do
this, follow the installation instructions of Alire, then you can add the
`gnatprove` dependency to an alire project using
```
    alr with gnatprove
```
Alire will download gnatprove if necessary.

## 3.3 The older GNAT Community version

There is an older community version of the tools, packaged with GNAT and
GNATStudio. You can download it from [AdaCore's
website](https://www.adacore.com/download).

# 4. Governance

SPARK is led by AdaCore and co-developed by AdaCore, Capgemini and Inria. The
SPARK team at AdaCore is responsible for the technology roadmap, taking into
account the needs of all stakeholders: sales and marketing, customers, other
development teams, community.

The team is organized around a set of roles for QA, integration, certification,
language evolution, etc. with two roles managing interactions:

The Team Coordinator:

* Defines the technology roadmap with all stakeholders.
* Coordinates and organizes the work in the team.
* Adjusts efforts and priorities based on the technology roadmap.

The Team Technical Authority:

* Provides and maintains deep knowledge of the technology.
* Is the main reference point for knowledge on the technology.
* Is the software architect on the technology.

Currently these roles are exercised by Claire Dross (Team Coordinator) and
Johannes Kanig (Team Technical Authority).

# 5. Community

News about SPARK project are shared primarily on [AdaCore's
blog](https://blog.adacore.com/). Questions and bug-reports are welcome
via the GitHub issue tracker.

# 6. Documentation

You can find the definition of the SPARK language in the
[SPARK Reference Manual](https://docs.adacore.com/live/wave/spark2014/html/spark2014_rm/index.html),
and instructions on how to use the tool, together with a tutorial, in the
[SPARK User's Guide](https://docs.adacore.com/live/wave/spark2014/html/spark2014_ug/index.html).

# 7. Building SPARK

Building gnatprove requires building the two projects `gnat2why` and `gnatprove`
in this repository, and the `why3` submodule containing the AdaCore fork of
Why3.

## Building `gnatprove` and `gnat2why`

This requires the following sources and libraries:
- Matching GNAT compiler
- Matching GNAT front-end sources made available in gnat2why/gnat_src
- gprbuild
- VSS
- sarif-ada
- libgpr2
- gnatcoll-core
- ada_toml

See the build instructions in the Makefile for details on how to build gnat2why
and gnatprove.

For FSF compiler and sources, we recommend using the `fsf` branch, or the
versioned `fsf-xx` branches for specific versions.

## Building Why3 (gnatwhy3)

Why3 needs a working opam setup. The dependencies are documented in the
AdaCore-maintained [Why3 fork](https://github.com/AdaCore/why3).

## Provers

GNATprove expects provers to be available. GNATprove will detect and
use Z3, cvc5 and alt-ergo when available in PATH, or installed in
PREFIX/libexec/spark/bin.

# 8 Working with source code

Since most of the source code is written in Ada an editor or IDE that has
dedicated support for Ada is recommended. Below are tips for some common IDEs.

## 8.1 Using GNAT Studio

Simply open the respective project, e.g., `gnatprove.gpr` or
`gnat2why/gnat2why.gpr`, from GNAT Studio or pass it to the executable using
the `-P` switch.

## 8.2 Using VS Code

The folder `.vscode` contains some settings and a [README](.vscode/README.md)
file that can be helpful when using VS Code.
