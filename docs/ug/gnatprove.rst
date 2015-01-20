.. _formal verification with gnatprove:

************************************
Formal Verification with |GNATprove|
************************************

The |GNATprove| tool is packaged as an executable called ``gnatprove``. Like
other tools in |GNAT Pro| Toolsuite, |GNATprove| is based on the structure of
GNAT projects, defined in ``.gpr`` files.

A crucial feature of |GNATprove| is that it interprets annotations exactly like
they are interpreted at run time during tests. In particular, their executable
semantics includes the verification of run-time checks, which can be verified
statically with |GNATprove|. |GNATprove| also performs additional verifications
on the specification of the expected behavior itself, and its correspondence to
the code.

How to Install |GNATprove|
==========================

We recommend to first install GPS (and optionally GNAT), and then install
|GNATprove| under the same location. Alternatively, you can install the
GNATbench plug-in for Eclipse instead of GPS, using the Eclipse installation
mechanism.

If you choose to install |GNATprove| in a different location, you should also
modify environment variables ``GPR_PROJECT_PATH`` (if you installed GNAT) and
``GPS_DOC_PATH`` (if you installed GPS). On Windows, edit the value of
``GPR_PROJECT_PATH`` under the Environnement Variables panel, and add to it the
value of ``<GNAT install dir>/lib/gnat``. Similarly, edit the value of
``GPS_DOC_PATH`` and add to it the value of ``<SPARK install
dir>/share/doc/spark``. On Linux/Mac with Bourne shell, use::

  export GPR_PROJECT_PATH=<GNAT install dir>/lib/gnat:$GPR_PROJECT_PATH
  export GPS_DOC_PATH=<SPARK install dir>/share/doc/spark:$GPS_DOC_PATH

or on Linux/Mac with C shell::

  setenv GPR_PROJECT_PATH <GNAT install dir>/lib/gnat:$GPR_PROJECT_PATH
  setenv GPS_DOC_PATH <SPARK install dir>/share/doc/spark:$GPS_DOC_PATH

See below for detailed installation instructions of GPS and |GNATprove|.

Installation under Windows
--------------------------

If not already done, first run the GPS installer by e.g. double clicking
on `gps-6.0.2-i686-pc-mingw32.exe` and follow the instructions.

.. note::

  If you're using GNAT GPL instead of GNAT Pro, you should run instead
  the GNAT GPL installer, which installs GPS.

Then similarly run the |GNATprove| installer, by e.g. double clicking on
`spark-15.0.2-x86-windows-bin.exe`.

You should have sufficient rights for installing the package (administrator
or normal rights depending on whether it is installed for all users or a
single user).

Installation under Linux/Mac
----------------------------

If not already done, you need to extract and install the GPS compressed
tarball and then run the install, e.g.::

  $ gzip -dc gps-6.0.2-x86_64-linux-bin.tar.gz | tar xf -
  $ cd gps-6.0.2-x86_64-linux-bin
  $ ./doinstall

Then follow the instructions displayed.

.. note::

  If you're using GNAT GPL instead of GNAT Pro, you should install instead
  the GNAT GPL package, which installs GPS.

Then do the same with the SPARK tarball, e.g.::

  $ gzip -dc spark-15.0.2-x86_64-linux-bin.tar.gz | tar xf -
  $ cd spark-15.0.2-x86_64-linux-bin
  $ ./doinstall

Note that you need to have sufficient rights for installing the package at the
chosen location (e.g. root rights for installing under /opt/spark).

How to Run |GNATprove|
======================

.. _Setting Up a Project File:

Setting Up a Project File
-------------------------

Basic Project Set Up
^^^^^^^^^^^^^^^^^^^^

If not already done, create a GNAT project file (`.gpr`), as documented in
the GNAT User's Guide, section `GNAT Project Manager`. See also
:ref:`Project_Attributes` for optional project attributes to specify the
proof directory and other |GNATprove| switches in the project file directly.

Note that you can use the project wizard from GPS to create a project file
interactively, via the menu :menuselection:`Project --> New...` See in
particular the first option (:menuselection:`Single Project`).

If you want to get started quickly, and assuming a standard naming scheme using
``.ads/.adb`` lower case files and a single source directory, then your project
file will look like:

.. code-block:: ada

  project My_Project is
     for Source_Dirs use (".");
  end My_Project;

saved in a file called ``my_project.gpr``.

Having Different Switches for Compilation and Verification
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In some cases, you may want to pass different compilation-level switches to
GNAT and |GNATprove|, for example use warning switches only for compilation, in
the same project file. In that case, you can use a scenario variable to specify
different switches for compilation and verification:

.. code-block:: ada

  project My_Project is

    type Modes is ("Compile", "Analyze");
    Mode : Modes := External ("MODE", "Compile");

    package Compiler is
       case Mode is
          when "Compile" =>
             for Switches ("Ada") use ...
          when "Analyze" =>
             for Switches ("Ada") use ...
       end case;
    end Compiler;

  end My_Project;

.. _Running GNATprove from the Command Line:

Running |GNATprove| from the Command Line
-----------------------------------------

|GNATprove| can be run from the command line as follows::

    gnatprove -P <project-file.gpr>

In the appendix, section :ref:`command line`, you can find an exhaustive list
of switches; here we only give an overview over the most common uses. Note that
|GNATprove| cannot be run without a project file.

When given a list of files, each of which contains a compilation unit,
|GNATprove| will analyze those units (including bodies and subunits)
plus the specifications and bodies of units on which they depend.

Two options modify this behavior:

* With option ``-u``, the bodies of dependent units are ignored, so only the
  given units and the specifications of dependent units are analyzed.

* With option ``-U``, all units of all projects are analyzed.

|GNATprove| consists of two distinct analyses, flow analysis and proof. Flow
analysis checks the correctness of aspects related to data flow (``Global``,
``Depends``, ``Abstract_State``, ``Initializes``, and refinement versions of
these), and verifies the initialization of variables. Proof verifies the
absence of run-time errors and the correctness of assertions such as ``Pre``
and ``Post`` aspects.  Using the switch ``--mode=<mode>``, whose possible
values are ``check``, ``flow``, ``prove`` and ``all``, you can choose which
analysis is performed:

* In mode ``check``, |GNATprove| checks that the program does not violate
  |SPARK| restrictions.

* In mode ``flow``, |GNATprove| checks that no uninitialized data is read in
  the program, and that the specified data dependencies and flow dependencies
  are respected in the implementation. Mode ``flow`` includes mode ``check``.
  This phase is called *flow analysis*.

* In mode ``prove``, |GNATprove| checks that the program is free from run-time
  errors, and that the specified functional contracts are respected in the
  implementation. Mode ``prove`` includes mode ``check``, as well as the part
  of mode ``flow`` which checks that no uninitialized data is read, to
  guarantees soundness of the proof results. This phase is called *proof*.

* In the default mode ``all``, |GNATprove| does both flow analysis and proof.

Using the option ``--limit-line=`` one can limit proofs to a particular file
and line of an Ada file. For example, if you want to prove only line 12 of
file ``example.adb``, you can add the option ``--limit-line=example.adb:12`` to
the call to |GNATprove|. Using the option ``--limit-subp=`` one can limit proofs
to a subprogram declared in a particular file at a particular line.

A number of options exist to influence the behavior for proof. Internally, the
prover(s) specified with option ``--prover`` is/are called repeatedly for each
check or assertion. Using the option ``--timeout``, one can change the maximal
time that is allocated to each prover to prove each check or assertion
(default: 1s). Using the option ``--steps`` (default: not used), one can set
the maximum number of reasoning steps that the prover is allowed to perform
before giving up. The ``steps`` option should be used when predictable results
are required, because the results with a timeout may differ depending on the
computing power or current load of the machine. The option ``-j`` activates
parallel compilation and parallel proofs.

The way checks are passed to the prover can also be influenced using the option
``--proof``. By default, the prover is invoked a single time for each check or
assertion (mode ``per_check``). This can be changed using mode ``per_path`` to
invoke the prover for each *path* that leads to the check. This option usually
takes much longer, because the prover is invoked much more often, but may give
better proof results. Finally, in mode ``progressive``, invoking the prover a
single time on the entire check is tried, and only if the check is not proved,
then other techniques that progressively consider each path in isolation
are tried.

The proof mode set with ``--proof`` can be extended with a qualifier ``all`` or
``lazy``, so that the entire switch may for example look like this:
``--proof=progressive:all``.  With this qualifier, one can select if proof
should stop at the first unproved formula (to save time) for a check or should
continue attempting to prove the other formulas related to the same check
(typically to identify more precisely which formulas are left unproved, which
can be then be handled with manual proof). The former is most suited for fully
automatic proof, it is the default value, and can be explicitly selected with
``lazy``. The latter is most suited for combination of automatic and manual
proof and can be selected with ``all``.

By default, |GNATprove| avoids reanalyzing unchanged files, on a
per-unit basis. This mechanism can be disabled with the option ``-f``.

By default, |GNATprove| stops at the first unit where it detect errors
(compilation errors, SPARK 2014 violations, or flow analysis errors).  The
option ``-k`` can be used to get |GNATprove| to issue errors of the same kind
for multiple units. If there are any `compilation` errors (really violations of
Ada legality rules here), |GNATprove| does not attempt analysis. If there are
violations of |SPARK| legality rules, or flow analysis errors, |GNATprove| does
not attempt proof.

Setting Up the Runtime Library
------------------------------

Just as other GNAT tools, |GNATprove| provides a ``--RTS=<runtime>`` switch
which allows to select the runtime library to be used along with the project
code.  |GNATprove| will search the runtime library in the following locations:

 * if the argument of the ``--RTS`` switch is a valid absolute or relative
   directory name, then this directory is interpreted as the runtime
   directory;
 * if not, |GNATprove| looks for the runtime library in the directory
   ``<spark-install>/share/spark/runtimes``.

The first option is the simplest, but the second one is more convenient, as the
same |GNATprove| command line can be used on different machines. However, it
requires copying the appropriate runtime library into the above-mentioned
directory. To do this, first find out the location of the target GNAT runtime
library.  You can use the ``<target>-gnatls -v`` command, and if you are using
the ``--RTS`` switch, specify it also when running gnatls.

For example, if you are using ``powerpc-vxworks-gnatmake`` as your builder and
``--RTS=kernel``, you can use::

    powerpc-vxworks-gnatls -v --RTS=kernel | grep adainclude

to find where the rts-kernel directory is located and then copy this directory
to the |GNATprove| installation, under::

    spark-prefix/share/spark/runtimes

.. _implementation_defined:

Implementation-Defined Behavior
-------------------------------

A |SPARK| program is guaranteed to be unambiguous, so that formal verification
of properties is possible. However, some behaviors (for example some
representation attribute values like the ``Size`` attribute) may depend on the
compiler used. By default, |GNATprove| adopts the same choices as the GNAT
compiler. |GNATprove| also supports other compilers by providing special
switches:

* ``-gnateT`` for specifying the target configuration
* ``--pedantic`` for warning about possible implementation-defined behavior

Note that |GNATprove| will always choose the smallest multiple of 8
bits for the base type, which is a safe and conservative choice for any Ada
compiler.

Target Parameterization
^^^^^^^^^^^^^^^^^^^^^^^

By default, |GNATprove| assumes that the compilation target is
the same as the host on which it is run, for setting target dependent
values, such as endianness or sizes and alignments of standard types.
If your target is not the same as the host on which you run |GNATprove|,
you might need to add the following to your project file::

  project My_Project is
     [...]
     package Compiler is
        for Switches ("Ada") use ("-gnateT=" & My_Project'Project_Dir & "/target.atp");
     end Compiler;
  end My_Project;

where ``target.atp`` is a file stored here in the same directory as the project
file ``my_project.gpr``, which contains the target parametrization. The format
of this file is described in the |GNAT Pro| User's Guide as part of the
``-gnateT`` switch description.

Target parameterization can be used:

* to specify a target different than the host on which |GNATprove| is run, when
  cross-compilation is used. If |GNAT Pro| is the cross compiler, the
  configuration file can be generated by calling the compiler for your target
  with the switch ``-gnatet=target.atp``. Otherwise, the target file should be
  generated manually.
* to specify the parameters for a different compiler than |GNAT Pro|, even when
  the host and target are the same. In that case, the target file should be
  generated manually.

Also by default, |GNATprove| uses the host run-time library, which may not be
suitable for your target when doing cross-compilation. A different run-time
library can be specified by calling |GNATprove| with the switch ``--RTS=dir``
where ``dir`` is the default location of the run-time library. The choice of
run-time library is described in the |GNAT Pro| User's Guide as part of the
description of switch ``--RTS`` for tool ``gnatmake``.

Parenthesized Arithmetic Operations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In Ada, non-parenthesized arithmetic operations could be re-ordered by the
compiler, which may result in a failing computation (due to overflow checking)
becoming a successful one, and vice-versa. By default, |GNATprove| evaluates
all expressions left-to-right, like GNAT. When the switch ``--pedantic`` is
used, a warning is emitted for every operation that could be re-ordered:

* any operand of a binary adding operation (+,-) that is itself a binary adding
  operation;
* any operand of a binary multiplying operation (\*,/,mod,rem) that is itself a
  binary multiplying operation.

.. _Running GNATprove from GPS:

Running |GNATprove| from GPS
----------------------------

|GNATprove| can be run from GPS. When |GNATprove| is installed and found on
your PATH, a :menuselection:`SPARK` menu is available with the following
entries:

.. csv-table::
   :header: "Submenu", "Action"
   :widths: 1, 4

   "Examine All",                "This runs |GNATprove| in flow analysis mode on all mains and the units they depend on in the project."
   "Examine All Sources",        "This runs |GNATprove| in flow analysis mode on all files in the project."
   "Examine File",               "This runs |GNATprove| in flow analysis mode on the current unit, its body and any subunits."
   "Prove All",                  "This runs |GNATprove| on all mains and the units they depend on in the project."
   "Prove All Sources",          "This runs |GNATprove| on all files in the project."
   "Prove File",                 "This runs |GNATprove| on the current unit, its body and any subunits."
   "Show Report",                "This displays the report file generated by |GNATprove|."
   "Clean Proofs",               "This removes all files generated by |GNATprove|."
   "Remove Editor Highlighting", "This removes highlighting generated by using |GNATprove|."

The three "Prove..." entries run |GNATprove| in the mode given by the project
file, or in the default mode "all" if no mode is specified.

The menus :menuselection:`SPARK --> Examine/Prove All` run |GNATprove| on all
main files in the project, and all files they depend on (recursively). Both
main files in the root project and in projects that are included in the root
project are considered. The menus :menuselection:`SPARK --> Examine/Prove All
Sources` run |GNATprove| on all files in all projects. On a project that has
neither main files nor includes other projects, menus :menuselection:`SPARK
--> Examine/Prove All` and :menuselection:`SPARK --> Examine/Prove All
Sources` are equivalent.

Keyboard shortcuts for these menu items can be set using the
:menuselection:`Edit --> Key Shortcuts` dialog in GPS.

.. note::

   The changes made by users in the panels raised by these submenus are
   persistent from one session to the other. Be sure to check that the selected
   checkboxes and additional switches that were previously added are still
   appropriate.

When editing an Ada file, |GNATprove| can also be run from a
:menuselection:`SPARK` contextual menu, which can be obtained by a right click:

.. csv-table::
   :header: "Submenu", "Action"
   :widths: 1, 4

   "Examine File",       "This runs |GNATprove| in flow analysis mode on the current unit, its body and any subunits."
   "Examine Subprogram", "This runs |GNATprove| in flow analysis mode on the current subprogram."
   "Prove File",         "This runs |GNATprove| on the current unit, its body and any subunits."
   "Prove Subprogram",   "This runs |GNATprove| on the current subprogram."
   "Prove Line",         "This runs |GNATprove| on the current line."
   "Prove Check",        "This runs |GNATprove| on the current failing condition. |GNATprove| must have been run at least once for this option to be available in order to know which conditions are failing."

|GNATprove| project switches can be edited from the panel ``GNATprove`` (in
:menuselection:`Project --> Edit Project Properties --> Switches`).

In some proof modes (``--proof=progressive`` or ``--proof=per_path``),
|GNATprove| attempts to prove checks separately for the possible paths leading
to a check. If the proof fails on a specific path, the user can display this
path in GPS by clicking on the icon to the left of the failed proof message, or
to the left of the corresponding line in the editor. The path is hidden again
when re-clicking on the same icon.

.. _GNATbench integration:

Running |GNATprove| from GNATbench
----------------------------------

|GNATprove| can be run from GNATbench. When |GNATprove| is installed and found
on your PATH, a :menuselection:`SPARK` menu is available with the following
entries:

.. csv-table::
   :header: "Submenu", "Action"
   :widths: 1, 4

   "Examine All",                "This runs |GNATprove| in flow analysis mode on all mains and the units they depend on in the project."
   "Examine All Sources",        "This runs |GNATprove| in flow analysis mode on all files in the project."
   "Examine File",               "This runs |GNATprove| in flow analysis mode on the current unit, its body and any subunits."
   "Prove All",                  "This runs |GNATprove| on all mains and the units they depend on in the project."
   "Prove All Sources",          "This runs |GNATprove| on all files in the project."
   "Prove File",                 "This runs |GNATprove| on the current unit, its body and any subunits."
   "Show Report",                "This displays the report file generated by |GNATprove|."
   "Clean Proofs",               "This removes all files generated by |GNATprove|."

The three "Prove..." entries run |GNATprove| in the mode given by the project
file, or in the default mode "all" if no mode is specified.

The menus :menuselection:`SPARK --> Examine/Prove All` run |GNATprove| on all
main files in the project, and all files they depend on (recursively). Both
main files in the root project and in projects that are included in the root
project are considered. The menus :menuselection:`SPARK --> Examine/Prove All
Sources` run |GNATprove| on all files in all projects. On a project that has
neither main files nor includes other projects, menus :menuselection:`SPARK
--> Examine/Prove All` and :menuselection:`SPARK --> Examine/Prove All
Sources` are equivalent.

.. note::

   The changes made by users in the panels raised by these submenus are
   persistent from one session to the other. Be sure to check that the selected
   checkboxes and additional switches that were previously added are still
   appropriate.

When editing an Ada file, |GNATprove| can also be run from a
:menuselection:`SPARK` contextual menu, which can be obtained by a right click:

.. csv-table::
   :header: "Submenu", "Action"
   :widths: 1, 4

   "Examine File",       "This runs |GNATprove| in flow analysis mode on the current unit, its body and any subunits."
   "Examine Subprogram", "This runs |GNATprove| in flow analysis mode on the current subprogram."
   "Prove File",         "This runs |GNATprove| on the current unit, its body and any subunits."
   "Prove Subprogram",   "This runs |GNATprove| on the current subprogram."
   "Prove Line",         "This runs |GNATprove| on the current line."

.. _GNATprove and Manual Proof:

|GNATprove| and Manual Proof
----------------------------

When automated provers fail to prove some condition that is valid, the validity
may be proved using a manual prover.

In the appendix, section :ref:`Alternative_Provers`, is explained how to use
different provers than the one |GNATprove| uses as default.

Manual proof in command line
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

When the prover used by |GNATprove| is configured as interactive, for each
analysed condition, either:

* It is the first time the prover is used on the condition then a file
  (containing the condition as input to the specified prover) is created in the
  project's proof directory (see :ref:`Project_Attributes`). |GNATprove|
  outputs a message concerning this condition indicating the file that was
  created. The created file should be edited by the user in order to prove the
  condition.

* The prover has already been used on this condition and the editable file
  exists. The prover is run on the file and the success or failure of the proof
  is reported in the same way it is done with the default prover.

.. note::

   Once a manual proof file is created and has been edited by the user, in
   order to run the prover on the file, the same prover must be once again
   specified to |GNATprove|. Once the condition is proved, the result will be
   saved in the why3 session so |GNATprove| won't need to be specified the
   prover again to know that the condition is valid.

Analysis with |GNATprove| can be limited to a single condition with the
``--limit-line`` option::

    gnatprove -P <project-file.gpr> --prover=<prover> --limit-line=<file>:<line>:<column>:<check-kind>

Where ``check-kind`` can be deduced from the message associated to the
failing condition reported by |GNATprove|:

.. UPDATES TO THIS TABLE SHOULD ALSO BE REFLECTED IN THE TABLE UNDER SECTION
.. "GNATprove Messages"

.. csv-table::
   :header: "Warning", "Check kind"
   :widths: 2, 1

   **run-time checks**
   "divide by zero might fail",                         "VC_DIVISION_CHECK"
   "array index check might fail",                      "VC_INDEX_CHECK"
   "overflow check might fail",                         "VC_OVERFLOW_CHECK"
   "range check might fail",                            "VC_RANGE_CHECK"
   "length check might fail",                           "VC_LENGTH_CHECK"
   "discriminant check might fail",                     "VC_DISCRIMINANT_CHECK"
   "tag check might fail",                              "VC_TAG_CHECK"

   **assertions**
   "initial condition might fail",                      "VC_INITIAL_CONDITION"
   "default initial condition might fail",              "VC_DEFAULT_INITIAL_CONDITION"
   "call to nonreturning subprogram might be executed", "VC_PRECONDITION"
   "precondition might fail",                           "VC_PRECONDITION"
   "precondition of main program might fail",           "VC_PRECONDITION_MAIN"
   "postcondition might fail",                          "VC_POSTCONDITION"
   "refined postcondition might fail",                  "VC_REFINED_POST"
   "contract case might fail",                          "VC_CONTRACT_CASE"
   "contract cases might not be disjoint",              "VC_DISJOINT_CONTRACT_CASES"
   "contract cases might not be complete",              "VC_COMPLETE_CONTRACT_CASES"
   "loop invariant might fail in first iteration",      "VC_LOOP_INVARIANT_INIT"
   "loop invariant might fail after first iteration",   "VC_LOOP_INVARIANT_PRESERV"
   "loop variant might fail",                           "VC_LOOP_VARIANT"
   "assertion might fail",                              "VC_ASSERT"
   "exception might be raised",                         "VC_RAISE"

   **Liskov Substitution Principle**
   "precondition might be stronger than class-wide precondition",               "VC_WEAKER_PRE"
   "precondition is stronger than the default class-wide precondition of True", "VC_TRIVIAL_WEAKER_PRE"
   "postcondition might be weaker than class-wide postcondition",               "VC_STRONGER_POST"
   "class-wide precondition might be stronger than overridden one",             "VC_WEAKER_CLASSWIDE_PRE"
   "class-wide postcondition might be weaker than overridden one",              "VC_STRONGER_CLASSWIDE_POST"


Manual proof in GPS
^^^^^^^^^^^^^^^^^^^

After running |GNATprove| with proof mode, the menu
:menuselection:`SPARK --> Prove Check` is available by right-clicking on a
check message in the location tab or by right-clicking on a line that fails
because of a single condition (i.e. there is only one check in the output of
|GNATprove| concerning this line).

In the dialog box, the field "Alternate prover" can be filled to use another
prover than Alt-Ergo. If the alternative prover is configured as
"interactive", after the execution of :menuselection:`SPARK --> Prove Check`,
GPS opens the manual proof file with the editor corresponding to the prover
under the condition that an editor is specified in the configuration of the
alternative prover.

Once the editor is closed, GPS re-executes
:menuselection:`SPARK --> Prove Check`. The user should verify the same
alternative prover as before is still specified. After execution, GPS will
offer to re-edit the file if the proof fails.

How to View |GNATprove| Output
==============================

Categories of Messages
----------------------

|GNATprove| issues four different kinds of messages: errors, warnings,
check messages and information messages.

* Errors are issued for |SPARK| violations or other language legality problems,
  or any other problem which does not allow to proceed to analysis.  Errors
  cannot be suppressed and must be fixed to proceed with analysis.

* Warnings are issued for any suspicious situation like unused values of
  variables, useless assignements, etc. Warnings are prefixed with the text
  ``"warning: "`` and can be suppressed with ``pragma Warnings``, see section
  :ref:`Suppressing Warnings`.

* Check messages are issued for any potential problem in the code which could
  affect the correctness of the program, such as missing initialization,
  possible failing run-time checks or unproved assertions. Checks come with a
  severity, and depending on the severity the message text is prefixed with
  ``"low: "``, ``"medium: "`` or ``"high: "``. Check messages cannot be
  suppressed like warnings, but they can be individually justified with pragma
  ``Annotate``, see section :ref:`Justifying Check Messages`.

* Information messages are issued for proved checks in some modes of
  |GNATprove|.

Effect of Mode on Output
------------------------

|GNATprove| can be run in four different modes, as selected with the switch
``--mode=<mode>``, whose possible values are ``check``, ``flow``, ``prove`` and
``all`` (see :ref:`Running GNATprove from the Command Line`). The output
depends on the selected mode.

In mode ``check``, |GNATprove| prints on the standard output error messages for
violations of |SPARK| restrictions on all the code for which ``SPARK_Mode`` is
``On``.

In modes ``flow`` and ``prove``, this checking is done as a first phase.

In mode ``flow``, |GNATprove| prints on the standard output messages for
possible reads of uninitialized data, mismatches betwen the specified data
dependencies and flow dependencies and the implementation, and suspicious
situations such as unused assignments and missing return statements. These
messages are all based on flow analysis.

In mode ``prove``, |GNATprove| prints on the standard output messages for
possible reads of uninitialized data (using flow analysis), possible run-time
errors and mismatches between the specified functional contracts and the
implementation (using proof).

In mode ``all``, |GNATprove| prints on the standard output both messages for
mode ``flow`` and for mode ``prove``.

If switch ``--report=all`` or ``--report=statistics`` is specified, |GNATprove|
additionally prints on the standard output information messages for proved
checks.

|GNATprove| generates global project statistics in file ``gnatprove.out``,
which can be displayed in GPS using the menu :menuselection:`SPARK --> Show
Report`. The statistics describe:

* which units were analyzed (with flow analysis, proof, or both)
* which subprograms in these units were analyzed (with flow analysis, proof, or
  both)
* the results of this analysis

Description of Messages
-----------------------

This section lists the different messages which |GNATprove| may output. Each
message points to a very specific place in the source code.  For example, if a
source file ``file.adb`` contains a division as follows::

      if X / Y > Z then ...

|GNATprove| may output a message such as::

   file.adb:12:37: medium: divide by zero might fail

where the division sign ``/`` is precisely on line 12, column 37. Looking at
the explanation in the first table below, which states that a division check
verifies that the divisor is different from zero, it is clear that the message
is about ``Y``, and that |GNATprove| was unable to prove that ``Y`` cannot be
zero. The explanations in the table below should be read with the context that
is given by the source location.

The following table shows the kinds of check messages issued by proof.

.. UPDATES TO THIS TABLE SHOULD ALSO BE REFLECTED IN THE TABLE UNDER SECTION
.. "Manual Proof in Command Line"

.. tabularcolumns:: |l|p{3in}|

.. csv-table::
   :header: "Message Kind", "Explanation"
   :widths: 1, 4

   **run-time checks**
   "divide by zero", "Check that the second operand of the division, mod or rem operation is different from zero."
   "index check", "Check that the given index is within the bounds of the array."
   "overflow check", "Check that the result of the given arithmetic operation is within the bounds of the base type."
   "range check", "Check that the given value is within the bounds of the expected scalar subtype."
   "length check", "Check that the given array is of the length of the expected array subtype."
   "discriminant check", "Check that the discriminant of the given discriminated record has the expected value. For variant records, this can happen for a simple access to a record field. But there are other cases where a fixed value of the discriminant is required."
   "tag check",          "Check that the tag of the given tagged object has the expected value."

   **assertions**
   "initial condition", "Check that the initial condition of a package is true after elaboration."
   "default initial condition", "Check that the default initial condition of a type is true after default initialization of an object of the type."
   "precondition", "Check that the precondition aspect of the given call evaluates to True."
   "call to nonreturning subprogram", "Check that the call to a subprogram called in case of error is unreachable."
   "precondition of main", "Check that the precondition aspect of the given main procedure evaluates to True after elaboration."
   "postcondition", "Check that the postcondition aspect of the subprogram evaluates to True."
   "refined postcondition", "Check that the refined postcondition aspect of the subprogram evaluates to True."
   "contract case", "Check that all cases of the contract case evaluate to true at the end of the subprogram."
   "disjoint contract cases", "Check that the cases of the contract cases aspect are all mutually disjoint."
   "complete contract cases", "Check that the cases of the contract cases aspect cover the state space that is allowed by the precondition aspect."
   "loop invariant in first iteration", "Check that the loop invariant evaluates to True on the first iteration of the loop."
   "loop invariant after first iteration", "Check that the loop invariant evaluates to True at each further iteration of the loop."
   "loop variant", "Check that the given loop variant decreases/increases as specified during each iteration of the loop. This implies termination of the loop."
   "assertion", "Check that the given assertion evaluates to True."
   "raised exception", "Check that the raise statement can never be reached."

   **Liskov Substitution Principle**
   "precondition weaker than class-wide precondition", "Check that the precondition aspect of the subprogram is weaker than its class-wide precondition."
   "precondition not True while class-wide precondition is True", "Check that the precondition aspect of the subprogram is True if its class-wide precondition is True."
   "postcondition stronger than class-wide postcondition", "Check that the postcondition aspect of the subprogram is stronger than its class-wide postcondition."
   "class-wide precondition weaker than overridden one", "Check that the class-wide precondition aspect of the subprogram is weaker than its overridden class-wide precondition."
   "class-wide postcondition stronger than overridden one", "Check that the class-wide postcondition aspect of the subprogram is stronger than its overridden class-wide postcondition."

.. insert blank line to separate more clearly the two tables in the HTML output

|

The following table shows all flow analysis messages, (E)rrors,
(W)arnings and (C)hecks.

.. tabularcolumns:: |p{3in}|l|p{3in}|

.. csv-table::
   :header: "Message Kind", "Class", "Explanation"
   :widths: 1, 1, 6

   "aliasing", "E", "Two formal or global parameter are aliased."
   "function with side effects", "E", "A function with side effects has been detected."
   "cannot depend on variable", "E", "Certain expressions (for example: discriminant specifications and component declarations) need to be variable free."
   "missing global", "E", "Flow analysis has detected a global that was not mentioned on the Global or Initializes aspects"
   "must be a global output", "E", "Flow analysis has detected an update of an in mode global."
   "pragma Elaborate_All needed", "E", "A remote state abstraction is used during the package's elaboration. Elaborate_All required for the remote package."
   "export must not depend on Proof_In", "E", "Flow analysis has detected an output of a subprogram that depends on a constant which is marked Proof_In."
   "class-wide mode must also be a class-wide mode of overridden subprogram", "E", "Miss-match between Global contracts of overridding and overridden subprograms."
   "class-wide dependency is not class-wide dependency of overridden subprogram", "E", "Miss-match between Depends contracts of overridding and overridden subprograms."
   "missing dependency", "C", "A dependency is missing from the dependency relation."
   "dependency relation", "C", "An out parameter or global is missing from the dependency relation."
   "missing null dependency", "C", "A variable is missing from the null dependency."
   "incorrect dependency", "C", "A stated dependency is not fulfilled."
   "not initialized", "C", "Flow analysis has detected the use of an uninitialized variable."
   "initialization must not depend on something", "C", "Wrong Initializes aspect detected."
   "type is not fully initialized", "C", "A type promised to be default initialized but is not."
   "needs to be a constituent of some state abstraction", "C", "Flow analysis detected a constituent that has to be exposed through some state abstraction."
   "is not modified", "W", "The variable is declared with mode in out, but is never modified, so could be declared with mode in."
   "unused assignment", "W", "Flow analysis has detected an assignment to a variable which is not read after the assignment."
   "initialization has no effect", "W", "Flow analysis has detected an object which is initialized, but never read."
   "this statement is never reached", "W", "This statement will never be executed (dead code)."
   "statement has no effect", "W", "Flow analysis has detected a statement which has no effect."
   "unused initial value", "W", "An in or in out parameter or global has been found which does not have any effect on any out or in out parameter or global."
   "unused", "W", "A global or locally declared variable is never used."
   "missing return", "W", "A return statement seems to be missing from the function."
   "no procedure exists that can initialize abstract state", "W", "Flow analysis detected a state abstraction that is impossible to initialize."
   "subprogram has no effect", "W", "A subprogram that has no exports has been detected."

.. note::

   Certain messages emitted by flow analysis are classified as errors
   and consequently cannot be suppressed or justified.

.. _How to Suppress or Justify Messages:

How to Suppress or Justify Messages
===================================

Like every sound and complete verification tool, |GNATprove| may issue false
alarms. A first step is to identify the type of message:

* warnings can be suppressed, see :ref:`Suppressing Warnings`
* check messages can be justified, see :ref:`Justifying Check Messages`

Check messages from proof may in fact correspond to provable checks, which
require interacting with |GNATprove| to find the correct contracts and/or
analysis switches, see :ref:`How to Investigate Unproved Checks`.

.. _Suppressing Warnings:

Suppressing Warnings
--------------------

|GNATprove| issues two kinds of warnings, which are controlled separately:

* Compiler warnings are controlled with the usual GNAT compilation switches:

  * ``-gnatws`` suppresses all warnings
  * ``-gnatwa`` enables all optional warnings
  * ``-gnatw?`` enables a specific warning denoted by the last character

    See the |GNAT Pro| User's Guide for more details. These should passed
    through the compilation switches specified in the project file.

* |GNATprove| specific warnings are controlled with switch ``--warnings``:

  * ``--warnings=off`` suppresses all warnings
  * ``--warnings=error`` treats warnings as errors
  * ``--warnings=continue`` issues warnings but does not stop analysis (default)

    The default is that |GNATprove| issues warnings but does not stop.

Both types of warnings can be suppressed selectively by the use of pragma
``Warnings`` in the source code. For example, |GNATprove| issues three warnings
on procedure ``Warn``, which are suppressed by the three pragma ``Warnings`` in
the source code:

.. literalinclude:: gnatprove_by_example/examples/warn.adb
   :language: ada
   :linenos:

Warnings with the specified message are suppressed in the region starting at
pragma ``Warnings Off`` and ending at the matching pragma ``Warnings On`` or at
the end of the enclosing scope. The ``Reason`` argument string is optional. A
regular expression can be given instead of a specific message in order to
suppress all warnings of a given form. Pragma ``Warnings Off`` can be added in
a configuration file to suppress the corresponding warnings across all units in
the project. Pragma ``Warnings Off`` can be specified for an entity to suppress
all warnings related to this entity.

Pragma ``Warnings`` can also take a first argument of ``GNAT`` or ``GNATprove``
to specify that it applies only to GNAT compiler or GNATprove. For example, the
previous example can be modified to use these refined pragma ``Warnings``:

.. literalinclude:: gnatprove_by_example/examples/warn2.adb
   :language: ada
   :linenos:

Besides the documentation benefit of using this refined version of pragma
``Warnings``, it makes it possible to detect useless pragma ``Warnings``, that
do not suppress any warning, with switch ``-gnatw.w``. Indeed, this switch can
then be used both during compilation with GNAT and formal verification with
GNATprove, as pragma ``Warnings`` that apply to only one tool can be identified
as such.

See the |GNAT Pro| Reference Manual for more details.

.. _Justifying Check Messages:

Justifying Check Messages
-------------------------

Check messages generated by |GNATprove|'s flow analysis or proof can be
selectively justified by adding a pragma ``Annotate`` in the source code. For
example, the check message about a possible division by zero in the return
expression can be justified as follows:

.. code-block:: ada

    return (X + Y) / (X - Y);
    pragma Annotate (GNATprove, False_Positive,
                     "divide by zero", "reviewed by John Smith");

The pragma has the following form:

.. code-block:: ada

    pragma Annotate (GNATprove, Category, Pattern, Reason);

where the following table explains the different entries:

.. tabularcolumns:: |l|p{4.5in}|

.. csv-table::
   :header: "Item", "Explanation"
   :widths: 1, 4

    "GNATprove",   "is a fixed identifier"
    "Category",    "is one of ``False_Positive`` or ``Intentional``"
    "Pattern",     "is a string literal describing the pattern of the check messages which shall be justified"
    "Reason",      "is a string literal providing a justification for reviews"

All arguments should be provided.

The *Category* currently has no impact on the behavior of the tool but serves a
documentation purpose:

* ``False_Positive`` indicates that the check cannot fail, although |GNATprove|
  was unable to prove it.

* ``Intentional`` indicates that the check can fail but that it is not
  considered to be a bug.

*Pattern* should be a substring of the check message to justify.

*Reason* is a string provided by the user as a justification for reviews. This
reason may be present in a |GNATprove| report.

Placement rules are as follows: in a statement list or declaration list, pragma
``Annotate`` applies to the preceding item in the list, ignoring other pragma
``Annotate``. If there is no preceding item, the pragma applies to the
enclosing construct. If the preceding or enclosing construct is a subprogram
body, the pragma applies to both the subprogram body and the spec including its
contract. This allows to place a justification for a check message issued by
|GNATprove| either on the spec when it is relevant for callers:

.. literalinclude:: gnatprove_by_example/examples/justifications.ads
   :language: ada
   :lines: 4-7

or on the body when it is an implementation choice that needs not be visible
to users of the unit:

.. literalinclude:: gnatprove_by_example/examples/justifications.ads
   :language: ada
   :lines: 9-10

.. literalinclude:: gnatprove_by_example/examples/justifications.adb
   :language: ada
   :lines: 10-16

How to Manage Assumptions
=========================

Because |GNATprove| analyzes separately subprograms and packages, its results
depend on assumptions about unanalyzed subprograms and packages. For example,
the verification that a subprogram is free from run-time errors depends on the
property that all the subprograms it calls implement their specified
contract. If a program is completely analyzed with |GNATprove|, cross-checking
of assumptions is mostly done automatically (with a few exceptions like
checking absence of infinite call chains). But in general, a program is partly
in |SPARK| and partly in other languages, mostly Ada, C and assembly
languages. Thus, assumptions on parts of the program that cannot be analyzed
with |GNATprove| need to be recorded for verification by other means, like
testing, manual analysis or reviews. When switch ``--assumptions`` is used,
|GNATprove| generates additional information about assumptions in its result
file ``gnatprove.out``:

.. tabularcolumns:: |l|p{4in}|

.. csv-table::
   :header: "Assumption Kind", "Explanation"
   :widths: 1, 3

   "post", "The subprogram guarantees that its postcondition holds."
   "aorte", "The subprogram is free from run-time errors."
   "effects", "The subprogram interacts with parameters and global variables
   as described in its spec (signature + data dependencies)."

.. _How to Write Subprogram Contracts:

How to Write Subprogram Contracts
=================================

|GNATprove| relies on contracts to perform its analysis. User-specified
subprogram contracts are assumed to analyze a subprogram's callers, and
verified when the body of the subprogram is analyzed.

But no contracts are compulsory. In the absence of user-provided contracts,
|GNATprove| internally generates default contracts, which may or not be
suitable depending on the verification objective:

* data dependencies (``Global``)

  See :ref:`Generation of Dependency Contracts`. The generated contract may be
  exact when completed from user-specified flow dependencies (Depends), or
  precise when generated from a body in SPARK, or coarse when generated from a
  body in full Ada.

* flow dependencies (``Depends``)

  See :ref:`Generation of Dependency Contracts`. The contract is generated from
  the user-specified or generated data dependencies, by considering that all
  outputs depend on all inputs.

* precondition (``Pre``)

  A default precondition of ``True`` is used in absence of a user-specified
  precondition.

* postcondition (``Post``)

  A default postcondition of ``True`` is used in absence of a user-specified
  postcondition, except for expression functions. For the latter, the body of
  the expression function is used to generate a matching postcondition. See
  :ref:`Expression Functions`.

Knowing which contracts to write depends on the specific verification
objectives to achieve.

.. _Generation of Dependency Contracts:

Generation of Dependency Contracts
----------------------------------

By default, |GNATprove| does not require the user to write data dependencies
(introduced with aspect ``Global``) and flow dependencies (introduced
with aspect ``Depends``), as it can automatically generate them from the
program.

.. note::

   |GNATprove| does not generate warning or check messages when the body of a
   subprogram does not respect a generated contract. Indeed, the generated
   contract is a safe over-approximation of the real contract, hence it is
   unlikely that the subprogram body respects it. The generated contract is
   used instead to verify proper initialization and respect of dependency
   contracts in the callers of the subprogram.

.. note::

   In absence of data dependencies, |GNATprove| does generate a contract using
   one of the techniques described in the following. To state that a subprogram
   has no data dependencies and prevent the automatic generation of data
   dependencies by |GNATprove|, a user should write an explicit ``Global =>
   null`` contract.

.. _Auto Completion for Incomplete Contracts:

Auto Completion for Incomplete Contracts
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

When only the data dependencies (resp. only the flow dependencies) are given on
a subprogram, |GNATprove| completes automatically the subprogram contract with
the matching flow dependencies (resp. data dependencies).

Writing Only the Data Dependencies
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

When only the data dependencies are given on a subprogram, |GNATprove|
completes them with flow dependencies that have all outputs depending on all
inputs. This is a safe over-approximation of the real contract of the
subprogram, which allows to detect all possible errors of initialization and
contract violation in the subprogram and its callers, but which may also lead
to false alarms because it is imprecise.

Take for example procedures ``Add`` and ``Swap`` for which data dependencies
are given, but no flow dependencies:

.. literalinclude:: gnatprove_by_example/examples/only_data_dependencies.ads
   :language: ada
   :linenos:

|GNATprove| completes the contract of ``Add`` and ``Swap`` with flow
dependencies that are equivalent to:

.. code-block:: ada

   procedure Add (X : Integer) with
     Global  => (In_Out => V),
     Depends => (V =>+ X);

   procedure Swap (X : in out Integer) with
     Global  => (In_Out => V),
     Depends => ((X, V) => (X, V));

Other flow dependencies with fewer dependencies between inputs and outputs
would be compatible with the given data dependencies of ``Add`` and
``Swap``. |GNATprove| chooses the contracts with the most dependencies. Here,
this corresponds to the actual contract for ``Add``, but to an imprecise
contract for ``Swap``:

.. literalinclude:: gnatprove_by_example/examples/only_data_dependencies.adb
   :language: ada
   :linenos:

This results in false alarms when |GNATprove| verifies the information flow
contract of procedure ``Call_Swap`` which calls ``Swap``, while it succeeds in
verifying the information flow contract of ``Call_Add`` which calls ``Add``:

.. literalinclude:: gnatprove_by_example/results/only_data_dependencies.flow
   :language: none

The most precise information flow contract for ``Swap`` would be:

.. code-block:: ada

   procedure Swap (X : in out Integer) with
     Global  => (In_Out => V),
     Depends => (V => X, X => V);

If you add this precise contract in the program, then |GNATprove| can also
verify the flow dependencies of ``Call_Swap``.

Note that the generated flow dependencies are used in the analysis of callers,
but |GNATprove| generates no warnings or check messages if the body of ``Add``
or ``Swap`` have fewer flow dependencies, as seen above. That's a difference
between these contracts being present in the code or auto completed.

Writing Only the Flow Dependencies
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

When only the flow dependencies are given on a subprogram, |GNATprove|
completes it with the only compatible data dependencies.

Take for example procedures ``Add`` and ``Swap`` as previously, expect now flow
dependencies are given, but no data dependencies:

.. literalinclude:: gnatprove_by_example/examples/only_flow_dependencies.ads
   :language: ada
   :linenos:

The body of the unit is the same as before:

.. literalinclude:: gnatprove_by_example/examples/only_flow_dependencies.adb
   :language: ada
   :linenos:

|GNATprove| verifies the data and flow dependencies of all
subprograms, including ``Call_Add`` and ``Call_Swap``, based on the completed
contracts for ``Add`` and ``Swap``.

Precise Generation for |SPARK| Subprograms
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

When no data or flow dependencies are given on a |SPARK| subprogram,
|GNATprove| generates precise data and flow dependencies by using
path-sensitive flow analysis to track data flows in the subprogram body:

 * if a variable is written completely on all paths in a subprogram body, it is
   considered an output of the subprogram; and
 * other variables that are written in a subprogram body are considered both
   inputs and outputs of the subprogram (even if they are not read explicitly,
   their output value may depend on their input value); and
 * if a variable is only read in a subprogram body, it is considered an input
   of the subprogram; and
 * all outputs are considered to potentially depend on all inputs.

Case 1: No Abstract State
~~~~~~~~~~~~~~~~~~~~~~~~~

Take for example a procedure ``Set_Global`` without contract which initializes
a global variable ``V`` and is called in a number of contexts:

.. literalinclude:: gnatprove_by_example/examples/gen_global.ads
   :language: ada
   :linenos:

.. literalinclude:: gnatprove_by_example/examples/gen_global.adb
   :language: ada
   :linenos:

|GNATprove| generates data and flow dependencies for procedure
``Set_Global`` that are equivalent to:

.. code-block:: ada

   procedure Set_Global with
     Global  => (Output => V),
     Depends => (V => null);

Note that the above contract would be illegal as given, because it refers to
global variable ``V`` which is not visible at the point where ``Set_Global`` is
declared in ``gen_global.ads``. Instead, a user who would like to write this
contract on ``Set_Global`` would have to use abstract state.

That generated contract for ``Set_Global`` allows |GNATprove| to both detect
possible errors when calling ``Set_Global`` and to verify contracts given by
the user on callers of ``Set_Global``. For example, procedure
``Set_Global_Twice`` calls ``Set_Global`` twice in a row, which makes the first
call useless as the value written in ``V`` is immediately overwritten by the
second call. This is detected by |GNATprove|, which issues two warnings on
line 18:

.. literalinclude:: gnatprove_by_example/results/gen_global.flow
   :language: none

Note that |GNATprove| also issues a warning on subprogram ``Do_Nothing`` which
has no effect, while it correctly analyzes that ``Set_Global`` has an effect,
even if it has the same signature with no contract as ``Do_Nothing``.

|GNATprove| also uses the generated contract for ``Set_Global`` to analyze
procedure ``Set_Global_Conditionally``, which allows it to verify the contract
given by the user for ``Set_Global_Conditionally``:

.. code-block:: ada

   procedure Set_Global_Conditionally (X : Boolean) with
     Global  => (Output => V),
     Depends => (V => X)

Case 2: Some Abstract State
~~~~~~~~~~~~~~~~~~~~~~~~~~~

In the presence of abstract state declared by the user, |GNATprove| generates
data and flow dependencies which take abstract state into account.

For example, take unit ``Gen_Global`` previously seen, where an abstract state
``State`` is defined for package ``Gen_Abstract_Global``, and refined into
global variable ``V`` in the body of the package:

.. literalinclude:: gnatprove_by_example/examples/gen_abstract_global.ads
   :language: ada
   :linenos:

.. literalinclude:: gnatprove_by_example/examples/gen_abstract_global.adb
   :language: ada
   :linenos:

We have chosen here to declare procedure ``Set_Global_Conditionally`` in
``gen_abstract_global.ads``, and so to express its user contract abstractly. We
could also have kept it local to the unit.

|GNATprove| gives the same results on this unit as before: it issues warnings
for the possible error in ``Set_Global_Twice`` and it verifies the contract
given by the user for ``Set_Global_Conditionally``:

.. literalinclude:: gnatprove_by_example/results/gen_abstract_global.flow
   :language: none

.. _Coarse Generation for non-SPARK Subprograms:

Coarse Generation for non-|SPARK| Subprograms
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

When no data or flow dependencies are given on a non-|SPARK| subprogram,
|GNATprove| generates coarser data and flow dependencies based on the
reads and writes to variables in the subprogram body:

 * if a variable is written in a subprogram body, it is considered both an
   input and an output of the subprogram; and
 * if a variable is only read in a subprogram body, it is considered an input
   of the subprogram; and
 * all outputs are considered to potentially depend on all inputs.

For example, take unit ``Gen_Global`` previously seen, where the body of
``Set_Global`` is marked with ``SPARK_Mode => Off``:

.. literalinclude:: gnatprove_by_example/examples/gen_ada_global.ads
   :language: ada
   :linenos:

.. literalinclude:: gnatprove_by_example/examples/gen_ada_global.adb
   :language: ada
   :linenos:

|GNATprove| generates a data and flow dependencies for procedure
``Set_Global`` that are equivalent to:

.. code-block:: ada

   procedure Set_Global with
     Global  => (In_Out => V),
     Depends => (V => V);

This is a safe over-approximation of the real contract for
``Set_Global``, which allows to detect all possible errors of initialization
and contract violation in ``Set_Global`` callers, but which may also lead to
false alarms because it is imprecise. Here, |GNATprove| generates a wrong
high message that the call to ``Set_Global`` on line 25 reads an uninitialized value
for ``V``:

.. literalinclude:: gnatprove_by_example/results/gen_ada_global.flow
   :language: none

This is because the generated contract for ``Set_Global`` is not precise
enough, and considers ``V`` as an input of the procedure. Even if the body of
``Set_Global`` is not in |SPARK|, the user can easily provide the precise
information to |GNATprove| by adding a suitable contract to ``Set_Global``,
which requires to define an abstract state ``State`` like in the previous
section:

.. code-block:: ada

   procedure Set_Global with
     Global  => (Output => State),
     Depends => (State => null);

With such a user contract on ``Set_Global``, |GNATprove| can verify the
contract of ``Set_Global_Conditionally`` without false alarms.

Writing Dependency Contracts
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Since |GNATprove| generates data and flow dependencies, you don't need
in general to add such contracts if you don't want to.

The main reason to add such contracts is when you want |GNATprove| to verify
that the implementation respects specified data dependencies and flow
dependencies. For those projects submitted to certification, verification of
data coupling and input/output relations may be a required verification
objective, which can be achieved automatically with |GNATprove| provided the
specifications are written as contracts.

Even if you write dependency contracts for the publicly
visible subprograms, which describe the services offered by the unit, there is
no need to write similar contracts on internal subprograms defined in the unit
body. |GNATprove| can generate data and flow dependencies on these.

Also, as seen in the previous section, the data and flow dependencies
generated by |GNATprove| may be imprecise, in which case it is necessary to add
manual contracts to avoid false alarms.

.. _Writing Contracts for Program Integrity:

Writing Contracts for Program Integrity
---------------------------------------

The most common use of contracts is to ensure program integrity, that is, the
program keeps running within safe boundaries. For example, this includes the
fact that the control flow of the program cannot be circumvented (e.g. through
a buffer overflow vulnerability) and that data is not corrupted (e.g. data
invariants are preserved).

Preconditions can be written to ensure program integrity, and in particular
they ensure:

* absence of run-time errors (AoRTE): no violations of language rules which
  would lead to raising an exception at run time (preconditions added to all
  subprograms which may raise a run-time error); and
* defensive programming: no execution of a subprogram from an unexpected state
  (preconditions added to subprograms in the public API, to guard against
  possible misuse by client units); and
* support of maintenance: prevent decrease in integrity (regressions, code rot)
  introduced during program evolution (preconditions added to internal
  subprograms, to guard against violations of the conditions to call these
  subprograms inside the unit itself); and
* invariant checking: ensure key data invariants are maintained throughout
  execution (preconditions added to all subprograms which may break the
  invariant).

For example, unit ``Integrity`` contains examples of all four kinds of
preconditions:

* Precondition ``X >= 0`` on procedure ``Seen_One`` ensures AoRTE, as otherwise
  a negative value for ``X`` would cause the call to ``Update`` to fail a range
  check, as ``Update`` expects a non-negative value for its parameter.
* Precondition ``X < Y`` on procedure ``Seen_Two`` ensures defensive
  programming, as the logic of the procedure is only correctly updating global
  variables ``Max`` and ``Snd`` to the two maximal values seen if parameters
  ``X`` and ``Y`` are given in strictly increasing order.
* Precondition ``X > Snd`` on procedure ``Update`` ensures support of
  maintenance, as this internal procedure relies on this condition on its
  parameter to operate properly.
* Precondition ``Invariant`` on procedure ``Update`` ensures invariant
  checking, as the property that ``Snd`` is less than ``Max`` expressed in
  ``Invariant`` should be always respected.

.. literalinclude:: gnatprove_by_example/examples/integrity.ads
   :language: ada
   :linenos:

.. literalinclude:: gnatprove_by_example/examples/integrity.adb
   :language: ada
   :linenos:

Note that ``pragma Assertion_Policy (Pre => Check)`` in ``integrity.ads``
ensures that the preconditions on the public procedures ``Seen_One`` and
``Seen_Two`` are always enabled at run time, while the precondition on internal
subprogram ``Update`` is only enabled at run time if compiled with switch
``-gnata`` (typically set only for debugging or testing). |GNATprove| always
takes contracts into account, whatever value of ``Assertion_Policy``.

|GNATprove| cannot verify that all preconditions on ``Integrity`` are
respected. Namely, it cannot verify that the call to ``Update`` inside
``Seen_One`` respects its precondition, as it is not known from the calling
context that ``Invariant`` holds:

.. literalinclude:: gnatprove_by_example/results/integrity.prove
   :language: none

Note that, although ``Invariant`` is not required to hold either on entry to
``Seen_Two``, the tests performed in if-statements in the body of ``Seen_Two``
ensure that ``Invariant`` holds when calling ``Update`` inside ``Seen_Two``.

To prove completely the integrity of unit ``Integrity``, it is sufficient to
add ``Invariant`` as a precondition and postcondition on every subprogram which
modifies the value of global variables ``Max`` and ``Snd``:

.. literalinclude:: gnatprove_by_example/examples/integrity_proved.ads
   :language: ada
   :linenos:

.. literalinclude:: gnatprove_by_example/examples/integrity_proved.adb
   :language: ada
   :linenos:

Here is the result of running |GNATprove|:

.. literalinclude:: gnatprove_by_example/results/integrity_proved.prove
   :language: none

.. _Writing Contracts for Functional Correctness:

Writing Contracts for Functional Correctness
--------------------------------------------

Going beyond program integrity, it is possible to express functional properties
of the program as subprogram contracts. Such a contract can express either
partially or completely the behavior of the subprogram. Typical simple
functional properties express the range/constraints for parameters on entry and
exit of subprograms (encoding their `type-state`), and the state of the
module/program on entry and exit of subprograms (encoding a safety or security
automaton). For those projects submitted to certification, expressing a
subprogram requirement or specification as a complete functional contract
allows |GNATprove| to verify automatically the implementation against the
requirement/specification.

For example, unit ``Functional`` is the same as ``Integrity_Proved`` seen
previously, with additional functional contracts:

* The postcondition on procedure ``Update`` (expressed as a ``Post`` aspect) is
  a complete functional description of the behavior of the subprogram. Note the
  use of an if-expression.
* The postcondition on procedure ``Seen_Two`` (expressed as a ``Post`` aspect)
  is a partial functional description of the behavior of the subprogram.
* The postcondition on procedure ``Seen_One`` (expressed as a
  ``Contract_Cases`` aspect) is a complete functional description of the
  behavior of the subprogram. There are three cases which correspond to
  different possible behaviors depending on the values of parameter ``X`` and
  global variables ``Max`` and ``Snd``. The benefit of expressing the
  postcondition as contract cases is both the gain in readability (no need to
  use ``'Old`` for the guards, as in the postcondition of ``Update``) and the
  automatic verification that the cases are disjoint and complete.

Note that global variables ``Max`` and ``Snd`` are referred to through public
accessor functions ``Max_Value_Seen`` and ``Second_Max_Value_Seen``. These
accessor functions can be declared after the contracts in which they appear, as
contracts are semantically analyzed only at the end of package declaration.

.. literalinclude:: gnatprove_by_example/examples/functional.ads
   :language: ada
   :linenos:

.. literalinclude:: gnatprove_by_example/examples/functional.adb
   :language: ada
   :linenos:

|GNATprove| manages to prove automatically almost all of these functional
contracts, except for the postcondition of ``Seen_Two`` (note in particular the
proof that the contract cases for ``Seen_One`` on line 10 are disjoint and
complete):

.. literalinclude:: gnatprove_by_example/results/functional.prove
   :language: none

Running |GNATprove| in mode ``per_path`` (see :ref:`Running GNATprove from the
Command Line` or :ref:`Running GNATprove from GPS`), and highlighting the path
on which the postcondition is not proved, shows that when the last branch of
the if-statement is taken, the following property is not proved::

  functional.ads:31:14: medium: postcondition might fail, requires Max_Value_Seen /= (Second_Max_Value_Seen)

Indeed, it could be the case that ``Max = Snd = 10`` on entry to procedure
``Seen_Two``, with values of parameters ``X = 1`` and ``Y = 2``, in which case
``Max`` and ``Snd`` would still be equal to 10 on exit. The missing piece of
information here is that ``Max`` and ``Snd`` are never equal, except when they
are both zero (the initial value). This can be added to function ``Invariant`` as follows:

.. literalinclude:: gnatprove_by_example/examples/functional_proved.adb
   :language: ada
   :lines: 7-8

With this more precise definition for ``Invariant``, all contracts are now
proved by |GNATprove|:

.. literalinclude:: gnatprove_by_example/results/functional_proved.prove
   :language: none

In general, it may be needed to further refine the preconditions of subprograms
to be able to prove their functional postconditions, to express either specific
constraints on their calling context, or invariants maintained throughout the
execution.

.. _Writing Contracts on Imported Subprograms:

Writing Contracts on Imported Subprograms
-----------------------------------------

Contracts are particularly useful to specify the behavior of imported
subprograms, which cannot be analyzed by |GNATprove|. It is compulsory to
specify in data dependencies the global variables these imported subprograms
may read and/or write, otherwise |GNATprove| assumes ``null`` data dependencies
(no global variable read or written).

.. note::

   A subprogram whose implementation is not available to |GNATprove|, either
   because the corresponding unit body has not been developed yet, or because
   the unit body is not part of the files analyzed by |GNATprove| (see
   :ref:`Specifying Files To Analyze` and :ref:`Excluding Files From
   Analysis`), is treated by |GNATprove| like an imported subprogram.

For example, unit ``Gen_Imported_Global`` is a modified version of the
``Gen_Abstract_Global`` unit seen previously in :ref:`Generation of Dependency
Contracts`, where procedure ``Get_Global`` is imported from C:

.. literalinclude:: gnatprove_by_example/examples/gen_imported_global.ads
   :language: ada
   :linenos:

Note that we added data dependencies to procedure ``Set_Global``, which can
be used to analyze its callers. We did not add flow dependencies, as
they are the same as the auto completed ones (see :ref:`Auto Completion for
Incomplete Contracts`).

.. literalinclude:: gnatprove_by_example/examples/gen_imported_global.adb
   :language: ada
   :linenos:

Note that we added an ``Address`` aspect to global variable ``V``, so that it
can be read/written from a C file.

|GNATprove| gives the same results on this unit as before: it issues warnings
for the possible error in ``Set_Global_Twice`` and it verifies the contract
given by the user for ``Set_Global_Conditionally``:

.. literalinclude:: gnatprove_by_example/results/gen_imported_global.flow
   :language: none

It is also possible to add functional contracts on imported subprograms, which
|GNATprove| uses to prove properties of their callers.  It is compulsory to
specify in a precondition the conditions for calling these imported subprograms
without errors, otherwise |GNATprove| assumes a default precondition of
``True`` (no constraints on the calling context). One benefit of these
contracts is that they are verified at run time when the corresponding
assertion is enabled in Ada (either with pragma ``Assertion_Policy`` or
compilation switch ``-gnata``).

.. note::

   A subprogram whose implementation is not in |SPARK| is treated by
   |GNATprove| almost like an imported subprogram, except that coarse data and
   flow dependencies are generated (see :ref:`Coarse Generation for non-SPARK
   Subprograms`). In particular, unless the user adds a precondition to such a
   subprogram, |GNATprove| assumes a default precondition of ``True``.

For example, unit ``Functional_Imported`` is a modified version of the
``Functional_Proved`` unit seen previously in :ref:`Writing Contracts for
Functional Correctness`, where procedures ``Update`` and ``Seen_One`` are
imported from C:

.. literalinclude:: gnatprove_by_example/examples/functional_imported.ads
   :language: ada
   :linenos:

.. literalinclude:: gnatprove_by_example/examples/functional_imported.adb
   :language: ada
   :linenos:

Note that we added data dependencies to the imported procedures, as
|GNATprove| would assume otherwise incorrectly ``null`` data dependencies.

As before, all contracts are proved by |GNATprove|:

.. literalinclude:: gnatprove_by_example/results/functional_imported.prove
   :language: none

.. _Contextual Analysis of Subprograms Without Contracts:

Contextual Analysis of Subprograms Without Contracts
----------------------------------------------------

It may be convenient to create local subprograms without necessarily specifying
a contract for these. |GNATprove| attempts to perform a contextual analysis of
these local subprograms without contract, at each call site, as if the code of
the subprograms was inlined. Thus, the analysis proceeds in that case as if it
had the most precise contract for the local subprogram, in the context of its
calls.

Let's consider as previously a subprogram which adds two to its integer input:

.. literalinclude:: gnatprove_by_example/examples/arith_with_local_subp.ads
   :language: ada
   :linenos:

And let's implement it by calling two local subprograms without contracts
(which may or not have a separate declaration), which each increment the input
by one:

.. literalinclude:: gnatprove_by_example/examples/arith_with_local_subp.adb
   :language: ada
   :linenos:

|GNATprove| would not be able to prove that the addition in
``Increment_In_Body`` or ``Increment_Nested`` cannot overflow in any
context. If it was using only the default contract for these subprograms, it
also would not prove that the contract of ``Add_Two`` is respected.  But since
it analyzes these subprograms in the context of their calls only, it proves
here that no overflow is possible, and that the two increments correctly
implement the contract of ``Add_Two``:

.. literalinclude:: gnatprove_by_example/results/arith_with_local_subp.prove
   :language: none
   :linenos:

This contextual analysis is available only for regular functions (not
expression functions) or procedures that are not externally visible (not
declared in the public part of the unit), without contracts (any of Global,
Depends, Pre, Post, Contract_Cases), and respect the following conditions:

 * does not contain nested subprogram or package declarations or instantiations
 * not recursive
 * not a generic instance
 * not defined in a generic instance
 * has a single point of return at the end of the subprogram
 * not called in an assertion or a contract
 * not called in a potentially unevaluated context
 * not called before its body is seen

If any of the above conditions is violated, |GNATprove| issues a warning to
explain why the subprogram could not be analyzed in the context of its calls,
and then proceeds to analyze it normally, using the default contract.

Note that it is very simple to prevent contextual analysis of a local
subprogram, by adding a contract to it, for example a simple ``Pre => True`` or
``Global => null``.

Otherwise, both flow analysis and proof are done for the subprogram in the
context of its calls.

.. _how to write loop invariants:

How to Write Loop Invariants
============================

As described in :ref:`loop invariants`, proving properties of subprograms
that contain loops may require the addition of explicit loop
invariant contracts. This section describes a systematic approach
for writing loop invariants.

The Four Properties of a Good Loop Invariant
--------------------------------------------

A loop invariant can describe more or less precisely the behavior of a
loop. What matters is that the loop invariant allows proving absence of
run-time errors in the subprogram, that the subprogram respects its contract,
and that the loop invariant itself holds at each iteration of the loop. There
are four properties that a good loop invariant should fulfill:

#. [INIT] It should be provable in the first iteration of the loop.

#. [INSIDE] It should allow proving absence of run-time errors and local
   assertions inside the loop.

#. [AFTER] It should allow proving absence of run-time errors, local assertions
   and the subprogram postcondition after the loop.

#. [PRESERVE] It should be provable after the first iteration of the loop.

As a first example, here is a variant of the search algorithm described in
:ref:`spark tutorial`, which returns whether a collection contains a desired
value, and if so, at which index. The collection is implemented as an array.

The specification of ``Linear_Search`` is given in file ``linear_search.ads``.
The postcondition of ``Search`` expresses that, either the search returns a
result within the array bounds, in which case it is the desired index,
otherwise the array does not contain the value searched.

.. literalinclude:: examples/linear_search_final/linear_search.ads
   :language: ada
   :linenos:

The implementation of ``Linear_Search`` is given in file ``linear_search.adb``.
The loop invariant of ``Search`` expresses that, at the end of each iteration,
if the loop has not been exited before, then the value searched is not in the
range of indexes between the start of the array ``A'First`` and the current
index ``Pos``.

.. literalinclude:: examples/linear_search_final/linear_search.adb
   :language: ada
   :linenos:

With this loop invariant, |GNATprove| is able to prove all checks in
``Linear_Search``, both those related to absence of run-time errors and those
related to verification of contracts:

.. literalinclude:: examples/results/linear_search_final.prove
   :language: none
   :linenos:

In particular, the loop invariant fulfills all four properties that we listed
above:

#. [INIT] It is proved in the first iteration (message on line 2).
#. [INSIDE] It allows proving absence of run-time errors inside the loop
   (messages on lines 1 and 4).
#. [AFTER] It allows proving absence of run-time errors after the loop
   (messages on lines 6 and 7) and the subprogram postcondition (message on
   line 5).
#. [PRESERVE] It is proved after the first iteration (message on line 3).

Note that the loop invariant closely resembles the second line in the
postcondition of the subprogram, except with a different range of values in the
quantification: instead of stating a property for all indexes in the array
``A``, the loop invariant states the same property for all indexes up to the
current loop index ``Pos``. In fact, if we equate ``Pos`` to ``A'Last`` for the
last iteration of the loop, the two properties are equal. This explains here
how the loop invariant allows proving the subprogram postcondition when the
value searched is not found.

Note also that we chose to put the loop invariant at the end of the loop. We
could as easily put it at the start of the loop. In that case, the range of
values in the quantification should be modified to state that, at the start of
each iteration, if the loop has not been exited before, then the value searched
is not in the range of indexes between the start of the array ``A'First`` and
the current index ``Pos`` *excluded*:

.. code-block:: ada

         pragma Loop_Invariant (for all K in A'First .. Pos - 1 => A (K) /= I);

Indeed, the test for the value at index ``Pos`` is done after the loop
invariant in that case.

We will now demonstrate techniques to complete a loop invariant so that it
fulfills all four properties [INIT], [INSIDE], [AFTER] and [PRESERVE], on a
more complex algorithm searching in an ordered collection of elements. Like the
naive search algorithm just described, this algorithm returns whether the
collection contains the desired value, and if so, at which index. The
collection is also implemented as an array.

The specification of this ``Binary_Search`` is given in file ``binary_search.ads``:

.. literalinclude:: examples/binary_search_no_loopinv/binary_search.ads
   :language: ada
   :linenos:

The implementation of ``Binary_Search`` is given in file ``binary_search.adb``:

.. literalinclude:: examples/binary_search_no_loopinv/binary_search.adb
   :language: ada
   :linenos:

Note that, although function ``Search`` has a loop, we have not given an
explicit loop invariant yet, so the default loop invariant of ``True`` will be
used by |GNATprove|. We are running |GNATprove| with a prover timeout of 60 seconds
(switch ``--timeout=60``) to get the results presented in the rest of this
section.

Proving a Loop Invariant in the First Iteration
-----------------------------------------------

Property [INIT] is the easiest one to prove. This is equivalent to proving a
pragma Assert in the sequence of statements obtained by unrolling the loop
once. In particular, if the loop invariant is at the start of the loop, this is
equivalent to proving a pragma Assert just before the loop. Therefore, the
usual techniques for investigating unproved checks apply, see :ref:`how to
investigate unproved checks`.

Completing a Loop Invariant to Prove Checks Inside the Loop
-----------------------------------------------------------

Let's start by running |GNATprove| on program ``Binary_Search`` without loop
invariant. It generates two medium message, on corresponding to a possible
run-time check failure, and one corresponding to a possible failure of
the postcondition:

.. literalinclude:: examples/results/binary_search_no_loopinv.prove
   :language: none

We will focus here on the message inside the loop, which corresponds to
property [INSIDE]. The problem is that variable ``Med`` varies in the loop, so
|GNATprove| only knows that its value is in the range of its type ``Index`` at
the start of an iteration (line 23), and that it is then assigned the value of
``Left + (Right - Left) / 2`` (line 24) before being used as an index into
array ``A`` (lines 26 and 28) and inside expressions assigned to ``Left`` and
``Right`` (lines 27 and 29).

As ``Left`` and ``Right`` also vary in the loop, |GNATprove| cannot use the
assignment on line 24 to compute a more precise range for variable ``Med``,
hence the message on index check.

What is needed here is a loop invariant that states that the values of ``Left``
and ``Right`` stay within the bounds of ``A`` inside the loop:

.. literalinclude:: examples/binary_search_range/binary_search.adb
   :language: ada
   :lines: 23-26

With this simple loop invariant, |GNATprove| now reports that the
check on lines 27 is now proved.
|GNATprove| computes that the value assigned to ``Med`` in the loop is also
within the bounds of ``A``.

Completing a Loop Invariant to Prove Checks After the Loop
----------------------------------------------------------

With the simple loop invariant given before, |GNATprove| still reports that the
postcondition of ``Search`` may fail, which corresponds to property [AFTER]. By
instructing |GNATprove| to prove checks progressively, as seens in
:ref:`proving spark programs`, we even get a precise message pointing to the
part of the postcondition that could not be proved:

.. literalinclude:: examples/results/binary_search_range.prove
   :language: none

Here, the message shows that the second line of the postcondition could not be
proved. This line expresses that, in the case where ``Search`` returns
``No_Index`` after the loop, the array ``A`` should not contain the value
searched ``I``.

One can very easily check that, if |GNATprove| can prove this property, it can
also prove the postcondition. Simply insert a pragma Assert after the loop
stating this property:

.. literalinclude:: examples/binary_search_post_assert/binary_search.adb
   :language: ada
   :lines: 35-38

|GNATprove| now succeeds in proving the postcondition, but it fails to prove
the assertion:

.. literalinclude:: examples/results/binary_search_post_assert.prove
   :language: none

The problem is that |GNATprove| only knows what the user specified about ``A``
in the precondition, namely that it is sorted in ascending order. Nowhere it is
said that ``A`` does not contain the value ``I``. Note that adding this
assertion is not compulsory. It simply helps identifying what is needed to
achieve property [AFTER], but it can be removed afterwards.

What is needed here is a loop invariant stating that, if ``A`` contains the
value ``I``, it must be at an index in the range ``Left..Right``, so when the
loop exits because ``Left > Right`` (so the loop test becomes false), ``A``
cannot contain the value ``I``.

One way to express this property is to state that the value of ``A`` at
index ``Left - 1`` is less than ``I``, while the value of ``A`` at index
``Right + 1`` is greater than ``I``. Taking into account the possibility that
there are no such indexes in ``A`` if either ``Left`` or ``Right`` are at the
boundaries of the array, we can express it as follows:

.. literalinclude:: examples/binary_search_naive/binary_search.adb
   :language: ada
   :lines: 23-28

|GNATprove| manages to prove these additional loop invariants, but it still
cannot prove the assertion after the loop. The reason is both simple and
far-reaching. Although the above loop invariant together with the property that
the array is sorted imply the property we want to express, it still requires
additional work for the prover to reach the same conclusion, which may prevent
automatic proof in the allocated time. In that case, it is better to express
the equivalent but more explicit property directly, as follows:

.. literalinclude:: examples/binary_search_precise/binary_search.adb
   :language: ada
   :lines: 23-31

|GNATprove| now proves the assertion after the loop. In general, it is simpler
to understand the relationship between the loop invariant and the checks that
follow the loop when the loop invariant is directly followed by the exit
statement that controls loop termination. In a "for" or "while" loop, this can
mean it is easier to place the Loop_Invariant pragmas at the *end* of the loop
body, where they precede the (implicit) exit statement.  In such cases, the loop
invariant is more likely to resemble the postcondition.

Proving a Loop Invariant After the First Iteration
--------------------------------------------------

With the loop invariant given before, |GNATprove| now reports that the loop
invariant of ``Search`` may fail after the first iteration, which corresponds
to property [PRESERVE]. By instructing |GNATprove| to prove checks
progressively, as seen in :ref:`proving spark programs`, we even get precise
messages pointing to the parts of the loop invariant that could not be proved:

.. literalinclude:: examples/results/binary_search_precise.prove
   :language: none

In general, the problem at this point is that the loop invariant is not precise
enough. The only information that |GNATprove| knows about the value of
variables that are modified in the loop, at each loop iteration, is the
information provided in the loop invariant. If the loop invariant is missing
some crucial information about these variables, which is needed to prove the
loop invariant after N iterations, |GNATprove| won't be able to prove that the
loop invariant holds at each iteration.

In loops that modify variables of composite types (records and arrays), it is
usually necessary at this stage to add in the loop invariant some information
about those parts of the modified variables which are not modified by the loop,
or which are not modified in the first N iterations of the loop. Otherwise,
|GNATprove| assumes that these parts may also be modified, which can prevent it
from proving the preservation of the loop invariant. See :ref:`loop invariants`
for an example where this is needed.

Here, there is nothing fundamental blocking |GNATprove| from proving that the
loop invariant holds after the first iteration. In those cases, it may be
necessary to guide the prover with intermediate assertions. A rule of thumb for
deciding which properties to assert, and where to assert them, is to try to
locate at which program point the prover does not success in proving the
property of interest, and to restate other properties that are useful for the
proof. Here, both kinds of assertions are needed by |GNATprove|. Here is the
implementation of ``Search`` with intermediate assertions:

.. literalinclude:: examples/binary_search_final/binary_search.adb
   :language: ada
   :linenos:

|GNATprove| proves all checks on this code. As this example shows, it can be
difficult to come up with a good loop invariant that allows proving
automatically all checks in a subprogram. Although this example is small, the
difficulty comes here from the complex properties stated by the user, which
involve multiple quantifiers. In cases where the difficulty is related to the
size of the loop rather than the complexity of the properties, it may be useful
to factor the loop into into local subprograms so that the subprograms'
preconditions and postconditions provide the intermediate assertions that are
needed to prove the loop invariant.


.. _Loop Patterns:

Loop Patterns
=============

As you gain experience in proving loops, you will find that you recognize
common *loop patterns*; you may recognize the code of loop bodies as well
as typical properties you want to prove for those loops, and the necessary
loop invariants. This section contains a collection of such commonly
occurring loop patterns. For each loop pattern we provide a brief
explanation followed by one or two examples. These loop patterns can be
used to minimize the time spent on loop proving. First we make a few notes
about loop patterns in general.

What Is the Proof Objective of Your Loop?
-----------------------------------------

The loop invariant and its complexity is greatly influenced by
the *proof objective of the loop*. When we say "proof objective of the
loop" this means the condition that needs to hold after the loop. If the
subprogram returns straight after the loop, then this is the same as the
postcondition of the subprogram. If there is some code in between the loop
and the end of the subprogram, then the "proof objective of the loop" is
the weakest precondition required for that code to ensure that the
postcondition of the subprogram holds.

Loop Pattern Granularity
------------------------

After studying some loop patterns, you will probably find patterns among
the loop patterns! In fact, all patterns described in this section can be
seen as instantiations of a very general loop pattern:

================  ========================
Loop Pattern      Loop Over Data Structure
================  ========================
Proof Objective   Establish property P.
Loop Behavior     Loops over the data structure and establishes P.
Loop Invariant    Property P is established for the part of the data structure
                  looped over so far.
================  ========================

However, it is useful to break this down into more detailed patterns since
often a small modification to the proof objective, or to the control
behavior of the loop, leads to a significantly changed loop invariant. In
the following, we focus on some loop patterns for scalar and array
properties that occur frequently in practice.

In the remainder of this section we identify the following loop
patterns:

#. :ref:`Initialization Patterns`

   a) default array initialization
   b) array initialization using dynamic expressions

#. :ref:`Validation Patterns`

   a) with early exit
   b) keep validating
   c) preserve flag

#. :ref:`Update Patterns`

   a) array update, basic
   b) array update, strong

#. :ref:`Search Patterns`

   a) linear
   b) binary

#. :ref:`Calculation Patterns`

   a) bounded summation

.. _Initialization Patterns:

Initialization Patterns
-----------------------

================  ========================
Loop Pattern      Array Initialization
================  ========================
Proof Objective   Every element of the array has a specific value.
Loop Behavior     Loops linearly over the array indexes and initializes every
                  element of the array.
                  The array to be initialized is an out parameter.
Loop Invariant    Every element initialized so far has its specific value.
================  ========================

Example: Default Array Initialization
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This example illustrates a common and basic form of array initialization
using a loop. The specification ``Init`` is given in the file
``init.ads``. Study the specification of the ``Default_Initialize``
subprogram:

.. literalinclude:: loop_patterns/default_initialisation_flow/init.ads
   :language: ada
   :linenos:

Note the typical proof objective of an array initialization in the
postcondition of ``Default_Initialize``. The implementation of
``Default_Initialize`` is given in the file ``init.adb``. Note the loop
invariant:

.. literalinclude:: loop_patterns/default_initialisation_flow/init.adb
   :language: ada
   :linenos:

The loop invariant follows the typical pattern of array initialization, and
is strong enough to prove that the loop fulfils the postcondition. We run
|GNATprove| with a prover timeout of 60 seconds (switch ``--timeout=60``)
and we have set the compiler flag to avoid intermediate overflows for
assertions (switch ``-gnato13``) to get the results presented throughout
this section. Inspection of the proof results confirms that the loop
invariant is correct; loop invariant initialization, loop invariant
preservation, as well as the postcondition, are all proved. However, we get
a few "medium" failed checks regarding initialization of the array ``A``:

.. literalinclude:: loop_patterns/results/default_initialisation_flow.prove
   :language: none
   :linenos:

Even though the proof of the loop is successful --- and this is our main
focus here --- |SPARK| static analysis has reported some flow
initialization issues. This particular case of data flow analysis problem
is sufficiently common to justify a minor sidetrack here:

*Sidenote about data flow errors for array initialization:* Sometimes the
early (pre proof) |SPARK| static analysis step called *data flow analysis*
produces false alarms about the possibility of an array not being entirely
initialized. This may be reported for example on access of an array element
inside a loop, or upon return of a subprogram with an out mode array
parameter. Proper initialization is required for sound proof, that is why
it is reported as a failed check. There are two ways to deal with these
false alarms about array initialization: 1) use an array aggregate for
initialization, or 2) justify the data flow error using pragma
``Annotate``. Be careful to only justify a reported issue if
you are convinced that it is a false alarm! Both approaches will be
illustrated when looking at array initialization patterns below.

For our default initialization example, after review of the loop code we
are convinced that this is a false alarm, and we put in the following two
justifications: Firstly, for the array access in the loop invariant in
the package body. Secondly, for the specification of
``Default_Initialize``:

.. literalinclude:: loop_patterns/default_initialisation_justified/init.adb
   :language: ada
   :linenos:

.. literalinclude:: loop_patterns/default_initialisation_justified/init.ads
   :language: ada
   :linenos:

Now, the data flow analysis step is completed without failed checks and the
|SPARK| tools proceed with successful proof:

.. literalinclude:: loop_patterns/results/default_initialisation_justified.prove
   :language: none
   :linenos:

Example: Array Initialization using a Dynamic Expression
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Sometimes you want to initialize every element of an array using an
arbitrary dynamic expression, which is not known at compile time. Consider
a dynamic variant of our previous example, called ``Dynamic_Initialize``:

.. literalinclude:: loop_patterns/dynamic_initialisation/init.ads
   :language: ada
   :linenos:

.. literalinclude:: loop_patterns/dynamic_initialisation/init.adb
   :language: ada
   :linenos:

Note here that the loop pattern is the same as for initialization using a
static value in the previous example. The new loop invariant and the proof
objective (in the post condition) still follow the pattern. There is a
notable difference in the program though: the precondition. Whenever you
calculate a dynamic expression, the precondition needs to be strong enough
to allow this calculation. Another difference is that this time we used an
array aggregate to create an initial "dummy" initialization which avoids any
data flow array initilization checks to fail. We get the following proof
result:

.. literalinclude:: loop_patterns/results/dynamic_initialisation.prove
   :language: none
   :linenos:

.. _Validation Patterns:

Validation Patterns
-------------------

Validation of sequences (arrays) is common in high integrity software. In
this section we will see how different proof objectives (or different loop
control flows) call for different patterns. First let us consider a
validation pattern where the loop terminates as soon as an invalid element
is encountered.

================  ========================
Loop Pattern      Sequence Validation with Early Exit
================  ========================
Proof Objective   Determine (flag) if there are any invalid elements in a given
                  array.
Loop Behavior     Loops linearly over the array elements and exits if an
                  invalid element is encountered.
Loop Invariant    Every element encountered so far is valid.
================  ========================

Example: Validate Sequence (Array)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. literalinclude:: loop_patterns/validation_early_exit/validation.ads
   :language: ada
   :linenos:

.. literalinclude:: loop_patterns/validation_early_exit/validation.adb
   :language: ada
   :linenos:

Note again how the post condition matches the proof objective of the loop
pattern, and the same for the loop invariant. We also get the expected
proof result:

.. literalinclude:: loop_patterns/results/validation_early_exit.prove
   :language: none
   :linenos:

===============  ===================================================
Loop Pattern     Sequence Validation that Validates Entire Structure
===============  ===================================================
Proof Objective  Determine (flag) if there are any invalid elements
                 in a given array.
Loop Behavior    Loops linearly over the array elements. If an invalid
                 element is encountered, flag this, but keep validating
                 (typically logging every invalidity) for the entire array.
Loop Invariant   If invalidity is not flagged, every element encountered so
                 far is valid.
===============  ===================================================

Note that even though we have the same proof objective (flag any
invalidity) as in the previous example, the control flow has changed not to
do early exit, and the loop invariant is different. The loop invariant of
the early exit pattern would be too strong and has been relaxed to an
implication.

Example: Validate Sequence, Keep Validating
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. literalinclude:: loop_patterns/validation_keep_validating/validation.ads
   :language: ada
   :linenos:

.. literalinclude:: loop_patterns/validation_keep_validating/validation.adb
   :language: ada
   :linenos:

As expected, we have successful proof results:

.. literalinclude:: loop_patterns/results/validation_keep_validating.prove
   :language: none
   :linenos:

===============  ==============================================
Loop Pattern     Sequence Validation Preserving Invalidity Flag
===============  ==============================================
Proof Objective  Determine (flag) if there are any invalid elements in
                 a given array, and preserve previously flagged alarm.
Loop Behavior    Loops linearly over the array elements. If an invalid
                 element is encountered, flag this, but keep validating
                 for the entire array and preserve previously flagged
                 alarm. The flag is an in out parameter.
Loop Invariant   If invalidity is not flagged, every element encountered
                 so far is valid. Preserve previously flagged alarm.
===============  ==============================================


A common usage pattern is to perform a sequence of validation operations,
for example at start-up, and collect all validation results in one flag:

.. code-block:: ada

  package body Startup
    with SPARK_Mode
  is
    procedure Initialize (Arr);

    procedure Do_Validation (Arr : in Arr_T; Success : out Boolean)
    is
    begin
      Success := True;

      Validate_This_Data (Arr, Success);

      Validate_That_Data (Arr, Success);

      Validate_This_Data_Too (Arr, Success);

    end Do_Validation;

end Startup;

Note here that the ``Success`` in out parameter is being used to pass on
previously flagged issues.

Example: Validate Sequence While Preserving Invalidity Flag
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The major difference from our earlier validation patterns is that this has
a stronger proof objective which also requires the program not to change
the in out alarm (Success) flag in an unsafe way.

.. literalinclude:: loop_patterns/validation_preserve_flag/validation.ads
   :language: ada
   :linenos:

The preservation of an alarm (``not Success``) is proved throughout the loop
using the ``'Loop_Entry`` attribute.

.. literalinclude:: loop_patterns/validation_preserve_flag/validation.adb
   :language: ada
   :linenos:

Again, we get successful proof result:

.. literalinclude:: loop_patterns/results/validation_preserve_flag.prove
   :language: none
   :linenos:


Example: Validate Sequence While Preserving Invalidity Flag --- Strong
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

So far we have seen validation patterns where the proof objective is
focused on safety properties. Safety properties are often formalised as an
implication that describes properties like "if no alarm is raised, then the
system is in a good state" or "if something bad happens, an alarm is
raised". These properties do not describe the entire functionality of the
subprogram, and can be fulfilled by overly "passive" programs for example a
program that does not do anything. Sometimes we want to make a full
function specification, and sometimes we work partially towards that goal,
to make a *stronger* proof objective.

================  ========================
Loop Pattern      Strong Sequence Validation Preserving Invalidity Flag
================  ========================
Proof Objective   The validity flag is True exactly when all the elements
                  are valid and previous validity was true.
Loop Behavior     Loops linearly over the array elements. If an invalid
                  element is encountered, flag this, but keep validating
                  for the entire array and preserve previously flagged
                  alarm. The flag is an in out parameter.
Loop Invariant    The validity flag is True exactly when all the elements
                  encountered so far are valid and previous validity was true.
================  ========================

.. literalinclude:: loop_patterns/validation_preserve_flag_strong/validation.ads
   :language: ada
   :linenos:

.. literalinclude:: loop_patterns/validation_preserve_flag_strong/validation.adb
   :language: ada
   :linenos:

And the proof is successful:

.. literalinclude:: loop_patterns/results/validation_preserve_flag_strong.prove
   :language: none
   :linenos:

.. _Update Patterns:

Update Patterns
---------------

================  ========================
Loop Pattern      Array Update --- Basic
================  ========================
Proof Objective   Elements of the array are updated according to
                  specified positions and with specified component values.
Loop Behavior     Loops over (a range of) array elements and assigns the
                  specified positions to values.
Loop Invariant    Every element assigned so far has been assigned at the
                  specified position and value.
================  ========================

Example: Array Update --- Basic
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. literalinclude:: loop_patterns/updates/update.ads
   :language: ada
   :linenos:

.. literalinclude:: loop_patterns/updates/update.adb
   :language: ada
   :linenos:

And the proof is successful:

.. literalinclude:: loop_patterns/results/updates.prove
   :language: none
   :linenos:

================  ========================
Loop Pattern      Array Update --- Strong
================  ========================
Proof Objective   Elements of the array are updated according to
                  specified positions and with specified component values.
                  Element not specified to be updated should have the same
                  value as on entry.
Loop Behavior     Loops over (a range of) array elements and assigns the
                  specified positions to values.
Loop Invariant    Every element assigned so far has been assigned at the
                  specified position and value. Element encountered so
                  far and not specified to be updated should have the same
                  value as on entry.
================  ========================

Example: Array Update --- Strong
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Similar to what we saw for the validation patterns we can specify stronger
proof objectives for array updates.

.. literalinclude:: loop_patterns/updates_strong/update.ads
   :language: ada
   :linenos:

.. literalinclude:: loop_patterns/updates_strong/update.adb
   :language: ada
   :linenos:

And the proof results:

.. literalinclude:: loop_patterns/results/updates_strong.prove
   :language: none
   :linenos:

.. _Search Patterns:

Search Patterns
---------------

We have seen earlier examples of linear and binary search, in the section
on :ref:`how to write loop invariants`.

================  ========================
Loop Pattern      Search with Early Exit
================  ========================
Proof Objective   Has found an element or position that meets a search
                  criterion.
Loop Behavior     Loops over the array elements. Exits when
                  found an element that meets the search criterion.
Loop Invariant    Every element encountered so far does not meet the search
                  criterion.
================  ========================

You may notice that this pattern has similarities with the validation
patterns. Together they can be called query patterns.

Example: Linear Wrap-Around Search of Table
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This time, let us make a slightly more complex example that searches for a
free slot over a table in a wrap-around fashion. This program uses two
consecutive loops, which illustrates that the "proof objective of the loop"
is not necessarily the same as the postcondition.

.. literalinclude:: loop_patterns/linear_search/find.ads
   :language: ada
   :linenos:

.. literalinclude:: loop_patterns/linear_search/find.adb
   :language: ada
   :linenos:

And we get the following proof results:

.. literalinclude:: loop_patterns/results/linear_search.prove
   :language: none
   :linenos:


Example: Linear Wrap-around Search of Table --- Strong
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Similarly to what we did for the validation patterns, let us strengthen the
proof objective towards full functional behavior:

.. literalinclude:: loop_patterns/linear_search_strong/find.ads
   :language: ada
   :linenos:

.. literalinclude:: loop_patterns/linear_search_strong/find.adb
   :language: ada
   :linenos:

Note that the proof objectives of the individual loops have not changed, but
the post condition that sums up the effects of the two loops has. We get
the following proof results:

.. literalinclude:: loop_patterns/results/linear_search_strong.prove
   :language: none
   :linenos:


Example: Binary Search SQRT
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This example uses binary search to find the interval of two consecutive
numbers squared, so that the given number lies therein. In every loop
iteration the search interval is halved and adjusted so that it gets
smaller while still containing the given number.

.. literalinclude:: loop_patterns/binary_search/sqrt.ads
   :language: ada
   :linenos:

The loop invariant states that for as much as the interval has been shrunk
so far, the given number lies therein.

.. literalinclude:: loop_patterns/binary_search/sqrt.adb
   :language: ada
   :linenos:

We get the following proof results:

.. literalinclude:: loop_patterns/results/binary_search.prove
   :language: none
   :linenos:

.. _Calculation Patterns:

Calculation Patterns
--------------------

================  ========================
Loop Pattern      Bounded Calculation
================  ========================
Proof Objective   Perform a calculation over all elements in a data structure
                  so that this is bounded.
Loop Behavior     Loops over the data structure, and uses the elements
                  to contribute to the calculated result.
Loop Invariant    The calculation performed so far is of a sufficiently small
                  bound so that the total bound can be met.
================  ========================

Example: Bounded Summation
^^^^^^^^^^^^^^^^^^^^^^^^^^

.. literalinclude:: loop_patterns/summation/summation.ads
   :language: ada
   :linenos:

Note that the precondition needs to be strong enough to ensure the total
bound can be met.

.. literalinclude:: loop_patterns/summation/summation.adb
   :language: ada
   :linenos:

Proof result:

.. literalinclude:: loop_patterns/results/summation.prove
   :language: none
   :linenos:

For more full-functional behavior specifications of calculations like
summation, usually lemmas or external axioms are necessary.

.. _How to Investigate Unproved Checks:

How to Investigate Unproved Checks
==================================

One of the most challenging aspects of formal verification is the analysis
of failed proofs. If |GNATprove| fails to prove automatically that a
run-time check or an assertion holds, there might be various reasons:

* [CODE] The check or assertion does not hold, because the code is wrong.
* [ASSERT] The assertion does not hold, because it is incorrect.
* [SPEC] The check or assertion cannot be proved, because of some missing
  assertions about the behavior of the program.
* [MODEL] The check or assertion is not proved because of current
  limitations in the model used by |GNATProve|.
* [TIMEOUT] The check or assertion is not proved because the prover
  timeouts.
* [PROVER] The check or assertion is not proved because the prover is not
  smart enough.

Investigating Incorrect Code or Assertion
-----------------------------------------

The first step is to check whether the code is incorrect [CODE] or the
assertion is incorrect [ASSERT], or both. Since run-time checks and assertions
can be executed at run time, one way to increase confidence in the correction
of the code and assertions is to test the program on representative inputs. The
following GNAT switches can be used:

* ``-gnato``: enable run-time checking of intermediate overflows
* ``-gnat-p``: reenable run-time checking even if ``-gnatp`` was used to
  suppress all checks
* ``-gnata``: enable run-time checking of assertions

Investigating Unprovable Properties
-----------------------------------

The second step is to consider whether the property is provable [SPEC]. A
check or assertion might be unprovable because a necessary annotation is
missing:

* the precondition of the enclosing subprogram might be too weak; or
* the postcondition of a subprogram called might be too weak; or
* a loop invariant for an enclosing loop might be too weak; or
* a loop invariant for a loop before the check or assertion might be too weak.

In particular, |GNATprove| does not look into subprogram bodies, so all the
necessary information for calls should be explicit in the subprogram
contracts. A focused manual review of the code and assertions can
efficiently diagnose many cases of missing annotations. Even when an
assertion is quite large, |GNATprove| precisely locates the part that it
cannot prove, which can help figuring out the problem. It may useful to
simplify the code during this investigation, for example by adding a
simpler assertion and trying to prove it.

|GNATprove| provides path information that might help the code review. You can
display inside the editor the path on which the proof failed, as described in
:ref:`Running GNATprove from GPS`. In many cases, this is sufficient to spot a
missing assertion. To further assist the user, we plan to add to this path some
information about the values taken by variables from a counterexample.

A property can also be conceptually provable, but the model used by
|GNATProve| can currently not reason about it [MODEL]. (See
:ref:`GNATProve_Limitations` for a list of the current limitations in
|GNATProve|.) In particular using the following features of the language
may yield VCs that should be true, but cannot be discharged:

* Subtypes of discriminated records
* Floating point arithmetic
* Bitwise operations for modular types
* The content of string literals

In these cases the missing information can usually be added using ``pragma
Assume``.

Investigating Prover Shortcomings
---------------------------------

The last step is to investigate if the prover would find a proof given enough
time [TIMEOUT] or if another prover can find a proof [PROVER]. To that end,
|GNATprove| provides options ``--timeout`` and ``--prover``, usable either from
the command-line (see :ref:`command line`) or inside GPS (see :ref:`Running
GNATprove from GPS`).

Note that for the above experiments, it is quite convenient to use the
:menuselection:`SPARK --> Prove Line` or :menuselection:`SPARK --> Prove
Subprogram` menus in GPS, as described in :ref:`Running GNATprove from GPS`, to
get faster results for the desired line or subprogram.

A common limitation of automatic provers is that they don't handle
non-linear arithmetic well. For example, they might fail to prove simple checks
involving multiplication, division, modulo or exponentiation.

In that case, a user may either:

* manually review the unproved checks and record that they can be trusted
  (for example by storing the result of |GNATprove| under version control),
  or
* add an assumption in the code to help the prover, in the form of a
  ``pragma Assume``. |GNATprove| assumes it holds, so does not attempt to
  prove it, and uses it in subsequent code. The assumption can be manually
  reviewed like mentioned above, and marking it as an assumption in the
  code helps documenting it, or
* instantiate a lemma which makes the missing property available.

The last is a technique which is a combination of expression functions and
``pragma Assume``. For example the below code is currently not provable
with Alt-Ergo using the default setup:

   .. literalinclude:: lemmas/example1.adb
      :language: ada
      :linenos:

This code can be made provable by using a lemma. All VCs for this function
are easily discharged, showing that the lemma holds in all cases.

   .. literalinclude:: lemmas/lemmas.ads
      :language: ada
      :linenos:

Note the postcondition on the expression function ensures that VCs are
generated showing it is always valid. The lemma can then be used though an
assumption (although it is planned to extend ``pragma Assert`` to support
this pattern):

   .. literalinclude:: lemmas/example2.adb
      :language: ada
      :linenos:

We plan to provide a `user view` of the formula passed to the prover, for
advanced users to inspect. This view will express in an Ada-like syntax the
actual formula whose proof failed, to make it easier for users to interpret
it. This format is yet to be defined.

For very advanced users, in particular those who would like to do manual
proof, we will provide a description of the format of the proof files
generated by |GNATprove|, so that users can understand the actual files
passed to the prover. Each individual file is stored under the
sub-directory ``gnatprove`` of the project object directory (default is the
project directory). The file name follows the convention::

  <file>_<line>_<column>_<check>_<num>.why

where:

* ``file`` is the name of the Ada source file for the check or assertion
* ``line`` is the line where the check or assertion appears
* ``column`` is the column
* ``check`` is an identifier for the check or assertion
* ``num`` is an optional number and identifies different paths through the
  program, between the start of the subprogram and the location of the check or
  assertion

For example, the proof files for a range check at line 160, column 42, of the
file ``f.adb`` are stored in::

  f.adb_160_42_range_check.why
  f.adb_160_42_range_check_2.why
  f.adb_160_42_range_check_3.why
  ...

The syntax of these files depend on the prover that was used. By default, it is
Alt-Ergo, so these files are in Why3 proof syntax.

To be able to inspect these files, you should instruct |GNATprove| to keep them
around by adding the switch ``-d`` to |GNATprove|'s command line. You can also
use the switch ``-v`` to get a detailed log of which proof files |GNATprove| is
producing and attempting to prove.

|GNATprove| by Example
======================

|GNATprove| is based on advanced technology for modular static analysis and
deductive verification. It is very different both from compilers, which do very
little analysis of the code, and static analyzers, which execute symbolically
the program. |GNATprove| does a very powerful local analysis of the program,
but it does not cross subprogram boundaries. Instead, it uses the
:ref:`Subprogram Contracts` provided by users to analyze calls. |GNATprove|
also requires sometimes that users direct the analysis with :ref:`Assertion
Pragmas`. Thus, it is essential to understand how |GNATprove| uses contracts
and assertion pragmas. This section aims at providing a deeper insight into how
|GNATprove|'s flow analysis and proof work, through a step-by-step exploration
of small code examples.

.. _basic_examples:

.. include:: gnatprove_by_example/basic.rst

.. _loop_examples:

.. include:: gnatprove_by_example/loop.rst

.. _manual_proof:

.. include:: gnatprove_by_example/manual_proof.rst

|SPARK| Examples in the Toolset Distribution
============================================

Further examples of |SPARK| are distributed with the |SPARK| toolset.
These are contained in the ``share/examples/spark`` directory
below the directory where the toolset is installed.

A subset of these examples can be accessed from the IDE (either
GPS or GNATBench) via the :menuselection:`Help --> SPARK --> Examples` menu
item.
