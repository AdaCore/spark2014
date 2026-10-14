##############
Tool Structure
##############

..
   devguide-meta:
   covers: overall tool pipeline, gnatprove orchestration, gnat2why modes,
   gnatwhy3 and why3server interfaces
   primary_code: src/gnatprove/, gnat2why/, why3/
   when_to_read: changes to tool orchestration, action scheduling, process
   boundaries, command-line plumbing, or cross-tool data flow

The SPARK tool is a tool that consists of several executables:

* gnatprove: This tool reads the command line, parses the project
  file, builds the set of analysis actions to run, invokes ``gnat2why`` on the
  required units, and calls the ``Spark_Report`` package to generate reports.
* gnat2why: It is invoked in two different modes. One mode generates global
  information, while the other performs flow analysis and proof. During the
  proof phase, gnat2why delegates some work to gnatwhy3.
* gnatwhy3: It processes a Why file and generates VCs that are then
  passed to provers via the why3server.
* why3server: A tool that takes care of spawning prover processes. It
  is better to have this in a dedicated tool instead of spawning them
  directly from gnatwhy3.
* the provers: Process prover input files and return proof results.
* spark_data_rep_wrapper, spark_semaphore_wrapper, and spark_memcached_wrapper:
  Wrap compiler or proof-tool invocations.

*********
gnatprove
*********

The gnatprove executable is the main entry point; it is the executable
that the user calls e.g. on the command line or from GNAT Studio. The
subsections explain the main steps performed by gnatprove.

Parsing the Command Line
========================

Gnatprove command-line parsing is complex because projects (including
withed projects) may contain the ``Prove.Switches`` attribute (legacy) or
``Prove.Proof_Switches``. To make things worse, command-line switches can
influence project parsing. It is therefore done in multiple steps.

The first step separates -cargs, handles all switches that cause gnatprove
to terminate immediately, such as ``--clean`` and ``--version``, and all
project-relevant switches (these are taken from GPR library). This phase
only passes the unhandled switches to the next phases. This phase uses
GNATCOLL.Opt_Parse to be able to reuse the GPR library switch definitions.

The next phase parses the command line and the root project's switch
attributes into records, then merges them to establish invocation-wide settings.
Each project's attributes are also processed into file-specific settings. For
scalar settings, precedence increases from ``Prove.Switches`` through
``Prove.Proof_Switches ("Ada")`` and ``Prove.Proof_Switches (file)`` to the command
line. List values accumulate, while flags are combined according to their value
kind in ``Merge_Parsed_Switches``.

Within each switch source, ``--level`` expands into detailed proof settings before
merging. Explicit detailed switches override that source's preset, but a
higher-precedence preset can override a lower-precedence detailed setting.
``Read_Command_Line`` in ``src/gnatprove/configuration.adb`` establishes the
initialization order; ``Switch_Multiplicity`` and ``Switch_Definitions`` document
repeated-switch behavior within a source separately from precedence across sources.

Undocumented switches
---------------------

The following switches are parsed by ``configuration.adb`` but intentionally
left out of the user-facing help (``share/spark/help.txt``). They are debugging
or internal-use switches:

``--benchmark``
   Run the analysis and prover executables through their ``fake_`` wrappers
   instead of the real ones (used by the testsuite for benchmarking).

``--debug-disable-prover-feedback``
   Suppress the explanatory prover-feedback text appended to unproved-check
   messages.

``--debug-list-explain-codes``
   Print every explain code with its one-line description and exit (used by the
   explain-codes test).

``--debug-no-cache-output``
   Omit the "from cache" phrase from check messages, for deterministic output.

``--debug-no-semaphore``
   Do not use a semaphore to limit the number of concurrent gnatwhy3 processes.

``--debug-prover-errors``
   Report errors raised by provers (forwarded as ``--debug-prover-errors`` to
   gnatwhy3).

``--exclude-line``
   Suppress the message emitted at a given ``file:line`` location.

``--ide-progress-bar``
   Emit progress-bar information for IDE integration.

``--why3-debug``
   Forward the given why3 debug flags to gnatwhy3 (as ``--debug-why3``).

``--why3-logging``
   Enable logging in the why3 layer (forwarded as ``--logging`` to gnatwhy3).

``--why3-server``
   Reuse an already-running why3server listening on the given socket instead of
   spawning a new one.

``--why3-stagger-ms``
   Pace prover launches for a single VC by forwarding the value as
   ``--stagger-ms`` to gnatwhy3. The tool-wide default is 250 milliseconds;
   when the switch is omitted, gnatprove forwards this default. An explicit
   value of 0 is not forwarded, so gnatwhy3 falls back to its own default of 0,
   which disables time-based staggering.

``--why3-stagger-window``
   Limit the number of provers launched concurrently for a single VC by
   forwarding the value as ``--stagger-window`` to gnatwhy3. The value must be
   positive when the switch is present.

``--z3-counterexample``
   Use Z3 (``z3_ce``) as the prover for counterexample generation.

Compilation switches reaching gnat2why
--------------------------------------

The analysis actions call ``gnat2why`` instead of the compiler, so only the
switch sources that these actions assemble explicitly are seen by the analysis:

* switches of the ``Compiler`` package are added by the GPR2 library itself,
  when the actions call the inherited ``Compute_Command``;
* switches following ``-cargs`` are appended by each action from
  ``CL_Switches.Cargs_List``;
* switches of the ``Builder.Global_Compilation_Switches`` attribute for Ada
  are read into ``Configuration.Global_Compilation_Switches`` when the project
  is loaded, and appended by each Ada action. Despite belonging to the
  ``Builder`` package, this attribute holds compilation switches, not options
  of the builder itself;
* all other switches of the ``Builder`` package are *not* taken into account.
  These describe how to build an executable rather than the program being
  analyzed: ``Builder.Switches`` and ``Builder.Default_Switches`` hold options
  of the builder, which each driver is responsible for interpreting, and their
  value is even keyed on the executable being built, a notion that has no
  equivalent in GNATprove.

Note that ``Builder.Global_Configuration_Pragmas`` does reach ``gnat2why``,
through the ``-gnatec`` switch added by the inherited ``Compute_Command`` of
the GPR2 library. This is intended, as configuration pragmas describe the
program to analyze; this is also how the User's Guide documents the way to
select assertion levels of the SPARK library.

The ``-gnateT`` switch, which describes the target of the analysis, is
singled out among the compilation switches: when the user specifies it, the
data-representation action is skipped altogether. That action runs the
compiler to generate code, which is impossible for a target that the compiler
at hand does not support.

Dependency graph and actions
============================

``gnatprove`` uses GPR2 project information to select compilation units and
construct a graph of actions. Each action invokes a tool on a unit:

* ``Global_Gen`` actions invoke ``gnat2why`` in global-generation mode, producing
  ALI files and ``.spark_error`` files for phase-1 diagnostics. They inherit
  ordinary source and configuration dependencies from GPR2's Ada compile action.
  For library projects, they also copy the ALI file to the library ALI directory
  when needed.
* ``Data_Rep`` actions invoke the target compiler through
  ``spark_data_rep_wrapper`` with ``-gnatR2js`` to produce representation JSON for
  the unit's existing body and specification. They depend on the same unit's ALI
  so they run only after successful global generation, avoiding secondary
  diagnostics after compilation errors.
* ``Analysis`` actions invoke ``gnat2why`` in analysis mode using the unit's own
  ALI and applicable ALI and representation files from its dependency closure.
  They produce ``.spark`` files containing analysis results.

The actions are scheduled together through ``GPR2.Build``. Additional dependencies
may be discovered when ``Global_Gen.Post_Execution`` reads ALI files; these extend
the inputs of dependent analysis actions. Incremental re-execution is handled by
the build engine through file dependencies and action signatures.

Generating data representation information
==========================================

Data-representation information is generated by dedicated build actions that
invoke the target compiler in a mode that emits JSON instead of object code.
These JSON files become inputs to the corresponding analysis actions, together
with the relevant ALI files.

The compiler invocation goes through ``spark_data_rep_wrapper``. This wrapper
suppresses compiler output in normal operation; compiler failures produce a
warning unless quiet mode is selected, and verbose mode shows compiler output.
It removes stale JSON files before invoking the compiler and writes empty fallback
files for any expected outputs missing after a compiler failure. The wrapper
returns success so that analysis can continue with the available representation
information.

These actions are only applicable when the compiler can generate code for the
target of the analysis. This is the case for a cross target described by its
own runtime, as the compiler of that target is then used, but not when the user
described the target with an explicit ``-gnateT`` switch: the compiler at hand
then generally cannot generate code for that target, so the actions are
skipped. Mode and source-layout restrictions are defined by ``Data_Rep.Applicable``
in ``src/gnatprove/gpr2-build-actions-process-compile-ada-data_rep.adb``.

Each JSON file is written next to the object files of the project that owns the
corresponding source, so the files of a withed project are not in the object
directory where its clients are analyzed. The analysis action therefore passes
the list of files that apply to a unit to gnat2why through the options file,
rather than letting gnat2why derive their names. That list is the same one that
the action declares as its inputs and hashes into its signature, so the build
graph, the staleness check and what gnat2why reads cannot drift apart; in
particular units excluded from the analysis, such as those of subprojects under
``--no-subprojects``, contribute no data representation even when files from an
earlier run are still lying around.

Passing options to gnat2why
===========================

``gnatprove`` passes tool-specific options to ``gnat2why`` through a JSON file
named by the ``-gnates`` switch. ``Gnat2Why_Opts.Writing`` writes this file and
``Gnat2Why_Opts.Reading`` reads it; ``Gnat2Why_Args`` is a compatibility rename of
the reader. The options contain the effective settings for the unit, including
``Global_Gen_Mode``, which selects global generation or analysis.

The filename is derived from a hash of the option values and participates in the
action's command line, so changed settings invalidate the action even though the
JSON contents are not command-line switches. ``Opt_File_Name`` in
``src/gnatprove/gnat2why_opts-writing.ads`` documents this contract.

``gnatprove`` also passes the target name, obtained by running the compiler with
``-dumpmachine``, so that ``Standard.Target_Name`` is properly defined.

Generating the Why3 configuration file
======================================

Before executing actions, ``gnatprove`` translates the shipped
``share/spark/config/gnatprove.conf`` into ``why3.conf``. It writes the file in the
artifact directory and the object directories of non-externally-built projects,
where ``gnatwhy3`` runs. Prover support libraries are built in the root project's
object directory, and the generated configurations reference that location.
``Write_Why3_Conf_File`` in ``src/gnatprove/gnatprove_build.adb`` documents the
schema, placeholders, and quoting rules. A user-supplied ``--why3-conf`` is read
by ``gnatwhy3`` as additional configuration and is not rewritten by ``gnatprove``.

Unit naming convention
======================

Manifest and analysis artifacts use different naming conventions:

- Proof manifests are named after, and matched to, the unit they describe by
  that unit's *manifest stem*: its dot-separated Ada name, lower-cased, with the
  dots written as dashes (so ``Foo.Bar`` becomes ``foo-bar``). The Ada unit name
  is taken from the driver rather than recovered from the source file name, so
  the stem is stable under a non-default naming scheme, where a unit's name and
  the name of the file it lives in differ.

- The ``.spark`` filename uses the main source file's base name, with a
  source-index suffix for multi-unit sources. The separator is given by
  ``Compiler.Multi_Unit_Object_Separator``. ``SPARK_Artifacts.Artifacts_Base_Name``
  defines this convention.

The two rules differ on purpose, because the artifacts are consumed differently.
A ``.spark`` file is tool-to-tool while a manifest is user-facing.

Proof manifests
===============

``gnatprove`` parses and validates manifests before analysis and passes normalized
policies through ``-gnates``. ``gnat2why`` resolves these policies against semantic
entities and records resolution warnings in ``.spark``; ``gnatwhy3`` receives the
concrete prover options selected by ``gnat2why``. The stage implementations are
``Configuration.Load_Proof_Manifest`` and ``Gnat2Why.Driver.Resolve_Proof_Manifest``.

After successful analysis, ``--generate-manifest-dir`` generates manifests from
the units recorded by the action graph and their existing ``.spark`` files.
It does not scan the object tree for analysis results. See the
`User's Guide manifest documentation
<https://docs.adacore.com/spark2014-docs/html/ug/en/source/how_to_run_gnatprove.html#manifest-files>`__
for the manifest format and options.

********
gnat2why
********

gnat2why has many tasks:
 - It generates global information (and is invoked in a special mode
   just for that);
 - It identifies SPARK code (in a phase called Marking);
 - It does flow analysis;
 - It checks ownership and borrowing permissions in a separate analysis;
 - It does (part of) proof;
 - It produces analysis results in the form of check messages.

Other chapters detail what happens in gnat2why. Here we mainly
focus on the interface of gnat2why with other programs.

``gnat2why`` is invoked by ``gnatprove`` on the relevant units in two modes:
once for global generation, then for analysis. As explained in the
:ref:`gnatprove` section, these invocations are now managed by
``gnatprove``'s build-action graph rather than by ``gprbuild``.

The "proof" part of gnat2why first serializes the GNAT tree to a Json
file. Then it invokes gnatwhy3 on that file. It reads back the results
of gnatwhy3 and interprets them to produce its own output on standard
output. Most command-line options for gnatwhy3 are computed by gnatprove and
passed to gnat2why through the JSON options file.

The machine-readable analysis artifacts are described in :ref:`report_generation`.

********************************
gnatwhy3, why3server and provers
********************************

gnatwhy3 reads the Gnat tree from a Json file as produced by gnat2why,
converts it to the tree of a Why3 program, uses the Why3 library to
generate verification conditions (VCs) from them, and to run provers on
the verification conditions. The :doc:`gnatwhy3` chapter describes its internals,
including :ref:`proof sessions <gnatwhy3_sessions>` and how existing proof attempts
are matched to new goals. Here we focus on the process interfaces.

- gnat2why: Gnat AST → Json-serialized Gnat AST
- gnatwhy3: Json-serialized Gnat AST → Gnat AST → Why3 AST
- why3: Why3 AST → Typed Why3 AST → …

The Why3 program that is generated by gnatwhy3 from the Gnat tree
depends only on the Why3 standard library and a few static files shipped
with SPARK, but not on other Why3 files produced by gnat2why or other
processes. gnatwhy3 processes Why3 tree and generates verification
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

The name of the socket (file system path on linux and name in a separate
namespace on windows) is passed to ``gnatwhy3`` by ``gnatprove`` via the
environment variable ``GNATPROVE_SOCKET``.

The only thing that gnatwhy3 runs via the server are prover processes.
Provers process a file in their own syntax or in SMTLib syntax, and
produce a simple answer (e.g. unsat or unknown). gnatwhy3 knows how to
interpret the textual answer of the prover and translates it to a
"proved/unproved" information.

When all prover processes are finished or have reached the timeout,
gnatwhy3 terminates and produces a result dictionary in JSON on
standard output.

``gnat2why`` spawns multiple instances of ``gnatwhy3`` in parallel. To bound their
memory use across analysis processes, ``gnatprove`` creates a semaphore before
proof actions run. Its capacity is ``max(1, Parallel / Num_Provers)``, where
``Num_Provers`` is the number of provers in the default file-specific configuration,
with a minimum of one. This limit is separate from why3server's prover limit.

Each ``gnatwhy3`` invocation is wrapped by ``spark_semaphore_wrapper``, which
acquires a token before running it and releases the token on exit. The semaphore
name is passed through ``GNATPROVE_SEMAPHORE``. ``--debug-no-semaphore`` disables
this wrapper, allowing many memory-intensive ``gnatwhy3`` processes to run at once.

.. _report_generation:

*****************
Report Generation
*****************

After build actions finish, including runs stopped by compilation errors,
``gnatprove`` calls ``Spark_Report.Generate_Report`` in the same process. It uses
the units recorded by the action graph to locate existing ``.spark`` files and
also reads the ``.spark_error`` files registered by global-generation actions.
The outputs are ``gnatprove.out`` for the textual summary and ``gnatprove.sarif``
for tool integration. The same analysis results are used by the manifest generator
and IDE integrations.

``gnat2why`` owns the diagnostic artifacts. Analysis writes flow, proof, warning,
and manifest-resolution results into ``.spark``. During global generation,
``Errout_Wrapper.Add_Frontend_Messages`` snapshots frontend diagnostics and
``Create_Error_JSON_File`` writes them into ``.spark_error``, including when
compilation errors prevent analysis. If a unit's ``.spark`` file exists, its
``.spark_error`` must contain no messages, to avoid duplicate diagnostics; report
loading asserts this invariant.

SARIF report generation
=======================

``src/gnatprove/spark_report-generate_sarif_report.adb`` converts these parsed
artifacts into SARIF. This is separate from the compiler's
``Erroutc.SARIF_Emitter`` in ``gnat2why/gnat_src/erroutc-sarif_emitter.adb``.
Compiler frontend diagnostics reach GNATprove's SARIF through ``.spark_error``.

The conversion preserves diagnostic arguments, related locations, suppressions,
and entity identity, and maps GNATprove severities to SARIF result kinds and
levels. ``Errout_Wrapper`` prepares message placeholders during JSON serialization;
the SARIF generator interprets those messages and supplies the rule descriptors.
When ``--flow-show-gg`` is enabled, generated contracts from ``.spark`` are exposed
as logical-location metadata.

GNATprove-specific metadata is stored under ``properties.gnatprove``. Explain
codes are carried by results when present on the diagnostic, and by rule
descriptors only for language violations with a stable rule-to-code mapping.
Each code is accompanied by its ``gnatprove --explain=E00NN`` command. Code
definitions and descriptions are in ``src/common/vc_kinds.ads``; long explanations
are in ``share/spark/explain_codes/E00NN.md``.

For field definitions, consult ``Properties``, ``Rules``, and
``Handle_SPARK_File`` in the SARIF generator. Source URI normalization is handled
by ``Make_Artifact_Location`` there and ``Sanity_Check_SARIF_Base_URI`` in
``configuration.adb``;
see the `User's Guide report documentation
<https://docs.adacore.com/spark2014-docs/html/ug/en/source/how_to_view_gnatprove_output.html>`__
for report options and ``--sarif-base-uri`` usage.

SARIF tests
-----------

SARIF regression tests live in ``testsuite/gnatprove/tests/`` and fall into
two categories.

The first category consists of SARIF-focused tests that inspect
``gnatprove.sarif`` directly. These tests generally use a dedicated
``test.py`` script and should validate the SARIF structure or custom metadata
as their primary purpose, rather than relying on the textual CLI output as a
proxy. The helper routines in
``testsuite/gnatprove/lib/python/test_support.py`` provide common accessors for
loading the report, iterating over SARIF results and rules, and extracting
custom properties such as ``gnatprove.reasonForCheck``,
``gnatprove.explainCode``, ``gnatprove.explainCommand``, or artifact-location
base-URI data.

When a SARIF field is also expected to appear in the CLI output, such a test
may add a secondary CLI check. In that case, ``test.out`` should print the
actual value extracted from SARIF, and also the CLI value when it is part of
the intended behavior. This keeps baselines uniform for tests that add custom
SARIF properties. For explain codes, SARIF tests should prefer checking
the rule-level descriptor metadata for language-violation rules only. For
warnings, flow diagnostics, front-end diagnostics, and fallback diagnostics,
tests should check the result-level property during the transition period and
verify that the rule descriptor does not carry explain-code metadata. Rule
descriptors should not use SARIF ``help`` for explain-code commands.

The second category consists of output-consistency tests driven by
``CheckSarifRefiner``. These tests are not meant to validate a specific SARIF
property. Instead, they check that the SARIF report remains aligned with the
normal GNATprove output: for each unsuppressed SARIF result, the message text
rendered from the SARIF result is expected to be present in the CLI output.
This catches cases where a diagnostic is emitted in SARIF but not in the
normal output, or where the two representations drift apart. The refiner uses
the current report mode as well: when ``--report=fail`` is in effect, SARIF
results of kind ``pass`` are ignored so that proved messages do not have to
appear in the filtered CLI output.

Some message families are intentionally excluded from this consistency check in
``test_support.py`` through ``ignore_patterns``. Those exclusions cover known
representation mismatches or diagnostics that are not yet rendered
consistently between SARIF and CLI output, so enabling the check does not mean
that every SARIF result is compared verbatim.

In tests written through ``test.yaml`` and the standard ``prove_all`` or
``do_flow`` helpers, setting ``enable_sarif_check: True`` requests this second
category of validation. The flag is translated internally into the default
refiner chain by adding ``CheckSarifRefiner`` after ``CheckMarksRefiner`` and
before the filtering/sorting refiners. This is a validation step only: it does
not modify the baseline output in ``test.out``. The generated SARIF report is
still examined only for consistency with the CLI output, not for individual
fields.

There are three important caveats for ``enable_sarif_check``.

 - If a test supplies an explicit ``refiners`` list in Python, that custom list
   overrides the boolean compatibility flags, so ``enable_sarif_check`` has no
   effect unless ``CheckSarifRefiner`` is added explicitly.
 - The helper code disables the SARIF consistency check automatically for
   SPARKlib tests and for runs that use ``--limit`` switches, because those
   modes do not currently interact well with SARIF output generation.
 - For tests whose purpose is to inspect SARIF-only data, use a dedicated
   ``test.py`` script and explicit SARIF queries instead of
   ``enable_sarif_check``.

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
