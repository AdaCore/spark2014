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

.. _Gnatprove:

*********
Gnatprove
*********

The gnatprove executable is the main entry point; it is the executable
that the user calls e.g. on the command line or from GPS. The
subsections explain the various phases of gnatprove.

Parsing the Command Line
========================

gnatprove needs to parse the project file to be able to fully interpret
switches, because the project file may also contain extra switches to
be passed to gnatprove. But some command line switches influence the
way the project is parsed. To break out of this circular dependency,
the command line is parsed twice:

 - Once only the actual command line (as in ``Ada.Command_Line``) is
   parsed for some switches that would terminate immediately such as
   ``--clean`` and ``--version``, and for switches that influence
   project parsing such as the ``-X`` switches and ``-aP``.
 - Then the actual command line is concatenated with the extra switches
   in the project file (if any), and the result is parsed again, now
   looking at all switches.

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
    relevant files is collected;
  - in the second phase, the above information is used to translate
    the SPARK code into Why.

In fact in both phases, the same executable ``gnat2why`` is called,
but the options are different so that the tool knows in which mode to
operate.

Using gprbuild
--------------

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
---------------------------

Because gnat2why is essentially a modified gcc and shares e.g. command
line parsing, it's not easy to add switches so that gnatprove can pass
information to gnat2why. So we added a single switch ``-gnates``,
which passes a single file in JSON format to gnat2why, that contains
all the extra information we need. The unit ``gnat2why_args`` handles
the reading and writing of that file.

The switch ``Global_Gen_Mode`` dictates if gnat2why is in Global
generation mode (first phase) or in translation mode (second phase).

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

