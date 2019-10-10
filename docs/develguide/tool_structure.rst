##############
Tool Structure
##############

The SPARK tool is a tool that consists of several executables:

* gnatprove: This tool reads the command line, parses the project
  file and finally (indirectly) calls gnat2why on each required source
  file of the project.
* gnat2why: It is in fact called twice on each file. In the first
  phase, it generates global information. In the second phase, flow
  analysis and proof are carried out. During the proof phase, gnat2why
  delegates some work to gnatwhy3.
* gnatwhy3: It processes a Why file and generates VCs that are then
  passed to provers via the why3server.
* whyserver: A tool that takes care of spawning prover processes. It
  is better to have this in a dedicated tool instead of spawning them
  directly from gnatwhy3.
* the provers: Process prover input files and return proof results.
* spark_report: A tool to generate a report file for the analysis results.

.. _gnatprove:

*********
gnatprove
*********

The gnatprove executable is the main entry point; it is the executable
that the user calls e.g. on the command line or from GNAT Studio. The
subsections explain the various phases of gnatprove.

Parsing the Command Line
========================

gnatprove needs to parse the project file to be able to fully interpret
switches, because the project file may also contain extra switches to
be passed to gnatprove. But some command line switches influence the
way the project is parsed. To break out of this circular dependency,
the command line is parsed several times:

 - Once only the actual command line (as in ``Ada.Command_Line``) is
   parsed for some switches that would terminate immediately such as
   ``--clean`` and ``--version``, and for switches that influence
   project parsing such as the ``-X`` switches and ``-aP``.
 - Then the actual command line is concatenated with the extra switches
   in the project file (if any), and the result is parsed again, now
   looking at all switches.
 - The previous step is repeated for all file-specific switches specified in
   the project file.

Inside ``configuration.adb``, there is a package ``CL_Switches`` that
represents command line switches (via command line or project file),
and there is a separate list of variables that represents synthesized
variables. For example, the timeout that will eventually be used by
gnatprove is synthesized from various command line switches, including
the ``--timeout`` switch.

.. _Generating Globals:

Generating Globals
==================

Processing of the SPARK source files happens in two phases:
  - in the first phase, information about global side effects of all
    relevant files is collected; this information is stored in ALI files.
  - in the second phase, the above information is used to translate
    the SPARK code into Why.

In fact in both phases, the same executable ``gnat2why`` is called,
but the options are different so that the tool knows in which mode to
operate.

Using gprbuild
==============

In fact, gnatprove doesn't know on which files to run ``gnat2why``
nor where to find the source files. It is best to delegate this task
to the builder tool ``gprbuild``. The idea is that ``gnat2why``
behaves just like a compiler (e.g. ``gcc``), so we only need to tell
gprbuild to call ``gnat2why`` instead of ``gcc``. This is done using
the ``--db`` switch. A directory is passed to ``gprbuild`` which
contains an .xml file that specifies a number of attributes. At the
minimum the ``Driver`` attribute must be set to ``gnatw2hy``.

``gnatwhy`` produces compiler-like output. But note that gprbuild
holds back the output of ``gnat2why`` until the tool has finished
completely. This can create some confusion in a debugging context.

Passing options to gnat2why
===========================

Because gnat2why is essentially a modified gcc and shares e.g. command
line parsing, it's not easy to add switches so that gnatprove can pass
information to gnat2why. So we added a single switch ``-gnates``,
which passes a single file in JSON format to gnat2why, that contains
all the extra information we need. The unit ``gnat2why_args`` handles
the reading and writing of that file.

The switch ``Global_Gen_Mode`` dictates if gnat2why is in Global
generation mode (first phase) or in translation mode (second phase).

Copying ALI files
=================

We call gprbuild twice using different settings. Gprbuild has some mechanisms
to avoid rerunning the compiler (gnat2why in our case), this includes
timestamps, the ``--complete-output`` mechanism, and rerunning when switches
have changes (``-s`` switch). Calling gprbuild twice with the same object
directory would partly break these mechanisms. Therefore we change the object
dir between those phases, adding the subdir ``phase1`` to the object dir of
``phase2``.

So that phase 2 can find the ALI files that have been produced in phase 1, we
copy them from ``<phase2objdir>/phase1`` to ``<phase2objdir>``, after having
run phase 1 and before running phase 2.

Running the Why3server
======================

The gnat2why tool (in translation mode) will call the gnatwhy3 tool,
which will spawn provers. However, the spawning of provers is
outsourced to the ``why3server`` tool. An instance of gnatwhy3
connects to the why3server and asks to spawn a prover. Many gnat2why/gnatwhy3
instances are spawned and can be running at the same time, but only
one why3server is running per invocation of gnatwhy3. This single
server instance is spawned here in ``gnatprove`` before running
``gnat2why`` in translation mode.

Translating to Why
==================

In this phase, gnat2why needs to be called in translation mode. This
happens in the same way as has been already described in the section
:ref:`Generating Globals`.

Generating the SPARK report
===========================

``gnatprove`` calls the ``spark_report`` tool to produce the
gnatprove.out file.

********
gnat2why
********

gnat2why has many tasks:
 - It generates global information (and is invoked in a special mode
   just for that);
 - It identifies SPARK code (in a phase called Marking);
 - It does flow analysis;
 - It does (part of) proof;
 - It produces analysis results in the form of check messages.

Other chapters detail what exatly happens in gnat2why. Here we mainly
focus on the interface of gnat2why with other programs.

gnat2why is invoked by gnatprove on all source files, twice. Once to
generate global information, then to do all the rest. As explained in
the :ref:`Gnatprove` section, gnatprove invokes gnat2why indirectly, via
gprbuild.

The "proof" part of gnat2why first translates the GNAT tree of a file
to a Why3 file. Then it invokes gnatwhy3 on that file. It reads back
the results of gnatwhy3 and interprets them to produce its own output
on standard output. Most of the command line options for gnatwhy3 are
in fact computed by gnatprove, and passed to gnat2why via the
``gnat2why_args`` mechanism.

In addition to the compiler-like output of gnat2why on standard
output, gnat2why produces a machine-parsable output in .spark files
(if the SPARK input unit is e.g. ``main.adb``, the corresponding
machine-parsable output is ``main.spark``).

********************************
gnatwhy3, why3server and provers
********************************

gnatwhy3 reads the Why3 file produced by gnat2why, generates
verification conditions (VCs) from them, and runs provers on the
verification conditions. A separate chapter describes how gnatwhy3
works. Here we mainly focus on the interface with other programs.

gnat2why produces a single file in Why3 format, that only depends on
the Why3 standard library and a few static files shipped with SPARK,
but not on other Why3 files produced by gnat2why or other processes.
gnatwhy3 reads and processes this file and generates verification
conditions in files. The format of these files depends on the prover
which is intended to be run on these files.

gnatwhy3 could spawn the prover processes directly, but for various
reasons it is better to delegate this to another process:

 - gnatwhy3 occupies a lot of memory, and spawning processes from a
   process with a lot of memory can be costly on Linux;
 - We want to run provers in parallel (when the user provides the -j
   switch), but gnatwhy3 is too deep in the call chain to know how
   many provers it is allowed to spawn in parallel. The why3server is
   at the top of the call chain and can spawn up to ``j`` provers.

gnatwhy3 connects to the server via a unix socket (on Unix) or a named
pipe (on Windows), using a custom protocol. The server receives the
command line to run from gnatwhy3, including a timeout. The server
returns the textual output of the command to gnatwhy3, or information
that the command has reached the timeout.

The only thing that gnatwhy3 runs via the server are prover processes.
Provers process a file in their own syntax or in SMTLib syntax, and
produce a simple answer (e.g. unsat or unknown). gnatwhy3 knows how to
interpret the textual answer of the prover and translates it to a
"proved/unproved" information.

When all prover processes are finished or have reached the timeout,
gnatwhy3 terminates and produces a result dictionary in JSON on
standard output.

************
spark_report
************

This tool is called when all gnat2why processes are finished. It reads
all ``.spark`` files (the machine-parsable output of gnat2why) and
produces a summary file ``gnatprove.out``.

gnatprove calls spark_report with a single argument, a filename. This file
contains some info for spark_report in JSON syntax, with the following
structure::

    obj_dirs : list of strings
    cmdline : list of strings
    switches : list of strings
    proof_switches : map of string to list of strings

Explanation for all fields:
 - obj_dirs: spark_report looks for all ``.spark`` files in each directory in
   the ``obj_dirs`` list, and processes them to generate the ``gnatprove.out``
   file.
 - cmdline: the switches given to gnatprove on the commandline.
 - switches: the switches of the ``Switches`` attribute in the ``Prove``
   package of the project file.
 - proof_switches: the switches for each index of the ``Proof_Switches``
   attribute in the ``Prove`` package.

***************
IDE Integration
***************

GNATprove can be called both from the command-line and from within one of the
two IDEs developed at AdaCore: GNAT Studio or GNATbench (a plugin of Eclipse).

A general principle is that as little logic as possible should be put in the
IDE support, as:
 - the support may be IDE-specific which entails duplication,
 - we may drop some IDE and add support for others in the future,
 - most features should be usable from the command-line, and
 - it is easier to test features from the command-line.

As an example, the generation of counterexample is attempted for all unproved
checks, and when successful a corresponding trace is added in the
:file:`.spark` file which lists the lines of code and values of variables which
constitute the counterexample in JSON format. The IDE integration consists
simply in displaying that information when requested by the user.

The IDE integration consists mostly in the following files inside ``gps``
repository, under ``share/plug-ins``:
 - file :file:`spark2014.py` defines the GNAT Studio integration
 - file :file:`spark2014/gnatprove.xml` defines the pop-up panels and Build
   Targets (shared between GNAT Studio and GNATbench)
 - file :file:`spark2014/gnatprove_menus.xml` defines the menus (shared between
   GNAT Studio and GNATbench)
 - file :file:`spark2014/itp_lib.py` defines the interactive proof support in
   GNAT Studio

In addition to the above XML files, the GNATbench integration consists in code
mapping the menus to actions inside Eclipse. The GNATbench integration is more
basic than the GNAT Studio one.
