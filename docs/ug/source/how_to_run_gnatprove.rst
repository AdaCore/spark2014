How to Run |GNATprove|
======================

.. _Setting Up a Project File:

Setting Up a Project File
-------------------------

Basic Project Set Up
^^^^^^^^^^^^^^^^^^^^

If not already done, create a GNAT project file (`.gpr`), as documented in the
|GNAT Pro| User's Guide, section `GNAT Project Manager`. See also :ref:`Project
Attributes` for optional project attributes to specify the proof directory and
other |GNATprove| switches in the project file directly.

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

With the above project, compilation is done using the ``Compile`` default
mode::

  gprbuild -P my_project.gpr

while formal verification is done using the ``Analyze`` mode::

  gnatprove -P my_project.gpr -XMODE=Analyze

.. _Running GNATprove from the Command Line:

Running |GNATprove| from the Command Line
-----------------------------------------

|GNATprove| can be run from the command line as follows::

    gnatprove -P <project-file.gpr>

In the appendix, section :ref:`Command Line Invocation`, you can find an
exhaustive list of switches; here we only give an overview over the most common
uses. Note that |GNATprove| cannot be run without a project file.

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
values are ``check``, ``check_all``, ``flow``, ``prove`` and ``all``, you can
choose which analysis is performed:

* In mode ``check``, |GNATprove| partially checks that the program does not
  violate |SPARK| restrictions. The benefit of using this mode prior to mode
  ``check_all`` is that it is much faster, as it does not require the results
  of flow analysis.

* In mode ``check_all``, |GNATprove| fully checks that the program does not
  violate |SPARK| restrictions, including checks not performed in mode
  ``check`` like the absence of side-effects in functions. Mode ``check_all``
  includes mode ``check``.

* In mode ``flow``, |GNATprove| checks that no uninitialized data is read in
  the program, and that the specified data dependencies and flow dependencies
  are respected in the implementation. Mode ``flow`` includes mode
  ``check_all``.  This phase is called *flow analysis*.

* In mode ``prove``, |GNATprove| checks that the program is free from run-time
  errors, and that the specified functional contracts are respected in the
  implementation. Mode ``prove`` includes mode ``check_all``, as well as the
  part of mode ``flow`` which checks that no uninitialized data is read, to
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
time that is allocated to each prover to prove each check or assertion.  Using
the option ``--steps`` (default: not used explicitly but set by default proof
level, see switch ``--level`` below), one can set the maximum number of
reasoning steps that the prover is allowed to perform before giving up. The
``steps`` option should be used when predictable results are required, because
the results with a timeout may differ depending on the computing power or
current load of the machine. The option ``-j`` activates parallel compilation
and parallel proofs. With ``-jnnn``, at most nnn cores can be used in
parallel. With the special value ``-j0``, at most N cores can be used in
parallel, when N is the number of cores on the machine.

.. note::

    When the project has a main file, or a file is passed as starting point to
    gnatprove, and the dependencies in the project are very linear (unit A
    depends only on unit B, which depends only on unit C, etc), then even when
    the ``-j`` switch is used, gnatprove may only consider one file at a time.
    This problem can be avoided by additionally using the ``-U`` switch.

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

Instead of setting individually switches that influence the speed and power of
proof, one may use the switch ``--level``, which corresponds to predefined
proof levels, from the faster level 0 (the default value) to the more powerful
level 4. More precisely, each value of ``--level`` is equivalent to directly
setting a collection of other switches discussed above:

* ``--level=0`` is equivalent to
  ``--prover=cvc4 --proof=per_check --steps=100``
* ``--level=1`` is equivalent to
  ``--prover=cvc4,z3,altergo --proof=per_check --steps=100``
* ``--level=2`` is equivalent to
  ``--prover=cvc4,z3,altergo --proof=per_check --steps=1000``
* ``--level=3`` is equivalent to
  ``--prover=cvc4,z3,altergo --proof=progressive --steps=1000``
* ``--level=4`` is equivalent to
  ``--prover=cvc4,z3,altergo --proof=progressive --steps=10000``

When ``--timeout=auto`` is used, a value of timeout is set depending on the
proof level:

* At levels 0 and 1, ``--timeout=auto`` is equivalent to ``--timeout=1``
* At levels 2 and 3, ``--timeout=auto`` is equivalent to ``--timeout=10``
* At level 4, ``--timeout=auto`` is equivalent to ``--timeout=60``

If both ``--level`` is set and an underlying switch is set (``--prover``,
``--steps``, or ``--proof``), the value of the latter takes precedence over the
value set through ``--level``.

By default, |GNATprove| avoids reanalyzing unchanged files, on a
per-unit basis. This mechanism can be disabled with the option ``-f``.

By default, |GNATprove| stops at the first unit where it detect errors
(violations of Ada or |SPARK| legality rules). The option ``-k`` can be used to
get |GNATprove| to issue errors of the same kind for multiple units. If there
are any violations of Ada legality rules, |GNATprove| does not attempt any
analysis. If there are violations of |SPARK| legality rules, |GNATprove| stops
after the checking phase and does not attempt flow analysis or proof.

When an error is detected (which does not included issuing check messages),
|GNATprove| returns with a non-zero exit status. Otherwise, |GNATprove| returns
with an exit status of zero, even when warnings and check messages are issued.

Using the GNAT Target Runtime Directory
---------------------------------------

If you are using GNAT as your target compiler, and the runtime used is
not compatible with |GNATprove|'s default runtime, you can use the GNAT
runtime directory from your GNAT installation, either directly or by
copying it to the |SPARK| installation.

To find the location of the target GNAT runtime, you can use the
``<target>-gnatls -v`` command, and if you are using the ``--RTS`` switch,
specify it also when running ``gnatls``.

If the argument of the ``--RTS`` switch passed to |GNATprove| is a valid
absolute or relative directory name, then |GNATprove| will use this directory
as the runtime directory.

Otherwise, |GNATprove| will search the runtime library in predefined
locations. There are two possible cases, depending on the kind of runtime used:

* Full runtime

  For example, if you are using ``powerpc-vxworks-gnatmake`` as your builder
  and ``--RTS=kernel``, then you can use:

  .. code-block:: sh

    powerpc-vxworks-gnatls -v --RTS=kernel | grep adalib

  To find where the :file:`rts-kernel` directory is located and then copy
  this directory to the |SPARK| installation, under
  :file:`<spark-install>/share/spark/runtimes`, for example
  using `bash` syntax:

  .. code-block:: sh

    cp -pr $(dirname $(powerpc-vxworks-gnatls -v --RTS=kernel | grep adalib)) \
      <spark-install>/share/spark/runtimes

  Then if not already present in your project file, you can then add
  the following:

  .. code-block:: ada

     package Builder is
        for Switches ("Ada") use ("--RTS=kernel");
     end Builder;

  Or alternatively if you are using a recent version of GNAT and |SPARK|,
  you can specify instead the runtime via the `Runtime` project attribute:

  .. code-block:: ada

    for Runtime ("Ada") use "kernel";

* Configurable runtime

  The simplest way to use configurable runtimes in |SPARK| is to install
  both |SPARK| and your cross GNAT compiler under the same root directory.

  If you do that and have in your project file the Target and Runtime
  properties set, then |GNATprove| (starting with version 16.0.1) will find the
  runtime automatically, e.g.:

  .. code-block:: ada

     for Target use "arm-eabi";
     for Runtime ("Ada") use "ravenscar-sfp-stm32f4";

  If you cannot use the above simple solution then you will first need to
  find the location of the GNAT configurable runtime using the following
  command:

  .. code-block:: sh

     <target>-gnatls -v --RTS=<runtime> | grep adalib

  which gives the path to :file:`<runtime directory>/adalib`.

  In the following example we want to use the ravenscar-sfp-stm32f4
  runtime library on arm-eabi target architecture:

  .. code-block:: sh

     arm-eabi-gnatls -v --RTS=ravenscar-sfp-stm32f4 | grep adalib

  This command gives the path to :file:`<ravenscar-sfp-stm32f4 runtime>/adalib`.

  You then need to copy (or make a symbolic link under Unix) the
  <ravenscar-sfp-stm32f4 runtime> directory to the |SPARK| installation, under
  :file:`<spark-prefix>/share/spark/runtimes`, for example using `bash`
  syntax:

  .. code-block:: sh

    cp -pr $(dirname $(arm-eabi-gnatls -v --RTS=ravenscar-sfp-stm32f4 | grep adalib)) \
      <spark-prefix>/share/spark/runtimes

  Then if not already present in your project file, you need to add the
  following:

  .. code-block:: ada

    for Runtime ("Ada") use "ravenscar-sfp-stm32f4";

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
* ``--pedantic`` for warnings about possible implementation-defined behavior

Note that, even with switch ``--pedantic``, |GNATprove| only detects some
implementation-defined behaviors. For more details, see the dedicated section
on how to :ref:`Ensure Portability of Programs`.

Note that |GNATprove| will always choose the smallest multiple of 8 bits for
the base type, which is a safe and conservative choice for any Ada compiler.

.. _Target Parameterization:

Target Parameterization
^^^^^^^^^^^^^^^^^^^^^^^

By default, |GNATprove| assumes that the compilation target is the same as the
host on which it is run, for setting target dependent values, such as
endianness or sizes and alignments of standard types.  If your target is not
the same as the host on which you run |GNATprove|, you have to tell
|GNATprove| the specificities of your target.

Note that the ``Target`` attribute of Project files is currently silently
ignored.

Instead, you need to add the following to your project file::

  project My_Project is
     [...]
     package Builder is
        for Global_Compilation_Switches ("Ada") use ("-gnateT=" & My_Project'Project_Dir & "/target.atp");
     end Builder;
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

.. _Parenthesized Arithmetic Operations:

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

Except from :menuselection:`Examine File` and :menuselection:`Prove File`, all
other submenus are also applicable to code inside generic units, in which case
the corresponding action is applied to all instances of the generic unit in the
project. For example, if a generic unit is instantiated twice, selecting
:menuselection:`Prove Subprogram` on a subprogram inside the generic unit will
apply proof to the two corresponding subprograms in instances of the generic
unit.

The menus :menuselection:`SPARK --> Examine ...` open a panel which allows
setting various switches for |GNATprove|'s analysis. The main choice offered in
this panel is to select the mode of analysis, among modes ``check``,
``check_all`` and ``flow`` (the default).

The menus :menuselection:`SPARK --> Prove ...` open a panel which allows
setting various switches for |GNATprove|'s analysis. By default, this panel
offers a few simple choices, like the proof level (see description of switch
``--level`` in :ref:`Running GNATprove from the Command Line`). If the user
changes its ``User profile`` for |SPARK| in :menuselection:`Edit -->
Preferences --> SPARK` from ``Basic`` to ``Advanced``, then a
more complex panel is displayed for proof, with more detailed switches.

|GNATprove| project switches can be edited from the panel ``GNATprove`` (in
:menuselection:`Project --> Edit Project Properties --> Switches`).

When proving a check fails on a specific path through a subprogram (for both
checks verified in flow analysis and in proof), |GNATprove| may generate path
information for the user to see. The user can display this path in GPS by
clicking on the icon to the left of the failed proof message, or to the left of
the corresponding line in the editor. The path is hidden again when re-clicking
on the same icon.

For checks verified in proof, |GNATprove| may also generate counterexample
information for the user to see (see :ref:`Understanding Counterexamples`). The
user can display this counterexample in GPS by clicking on the icon to the left
of the failed proof message, or to the left of the corresponding line in the
editor. The counterexample is hidden again when re-clicking on the same icon.

.. _Running GNATprove from GNATbench:

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

Manual Proof in Command Line
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

When the prover used by |GNATprove| is configured as interactive, for each
analysed condition, either:

* It is the first time the prover is used on the condition then a file
  (containing the condition as input to the specified prover) is created in the
  project's proof directory (see :ref:`Project Attributes`). |GNATprove|
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
.. "Description of Messages"

.. csv-table::
   :header: "Warning", "Check kind"
   :widths: 2, 1

   **run-time checks**
   "divide by zero might fail",                            "VC_DIVISION_CHECK"
   "array index check might fail",                         "VC_INDEX_CHECK"
   "overflow check might fail",                            "VC_OVERFLOW_CHECK"
   "range check might fail",                               "VC_RANGE_CHECK"
   "predicate check might fail",                           "VC_PREDICATE_CHECK"
   "predicate check might fail on default value",          "VC_PREDICATE_CHECK_ON_DEFAULT_VALUE"
   "length check might fail",                              "VC_LENGTH_CHECK"
   "discriminant check might fail",                        "VC_DISCRIMINANT_CHECK"
   "tag check might fail",                                 "VC_TAG_CHECK"
   "ceiling priority might not be in Interrupt_Priority",  "VC_CEILING_INTERRUPT"
   "interrupt might be reserved",                          "VC_INTERRUPT_RESERRED"
   "ceiling priority protocol might not be respected",     "VC_CEILING_PRIORITY_PROTOCOL"
   "task might terminate",                                 "VC_TASK_TERMINATION"

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
