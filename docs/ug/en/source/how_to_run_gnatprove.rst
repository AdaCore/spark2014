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
interactively, via the menu :menuselection:`File --> New Project...`.
In the dialog, see in particular the default option (:menuselection:`Single Project`).

If you want to get started quickly, and assuming a standard naming scheme using
``.ads/.adb`` lower case files and a single source directory, then your project
file will look like:

.. code-block:: gpr

  project My_Project is
     for Source_Dirs use (".");
  end My_Project;

saved in a file called ``my_project.gpr``.

.. _Having Different Switches for Compilation and Verification:

Having Different Switches for Compilation and Verification
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In some cases, you may want to pass different compilation-level switches to
GNAT and |GNATprove|, for example use warning switches only for compilation, in
the same project file. In that case, you can use a scenario variable to specify
different switches for compilation and verification:

.. code-block:: gpr

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

There are essentially three common ways you can select the files which will
be analyzed by |GNATprove|:

* Analyze everything::

     gnatprove -P <project-file.gpr> -U

  With switch ``-U``, all units of all projects in the project tree are
  analyzed. This includes units that are not used yet.

  This is usually what you want to use for an overnight analysis of a
  complex project.

* Analyze this project::

     gnatprove -P <project-file.gpr>

  All main units in the project and all units they (recursively) depend on
  are analyzed. If there are no main units specified, analyze all files in
  the project.

  This is what you want to use for the analysis of a particular executable
  only, or if you want to analyze different executables within a complex
  project with different options.

* Analyze files::

     gnatprove -P <project-file.gpr> [-u] FILES...

  If ``-u`` is specified, we only analyze the given files. If ``-u`` is not
  specified, we also analyze all units these files (recursively) depend on.

  This is intended for the day-to-day command-line or IDE use of
  |GNATprove| when implementing a project.

|GNATprove| consists of two distinct analyses: flow analysis and proof.
Flow analysis checks the correctness of aspects related to data flow
(``Global``, ``Depends``, ``Abstract_State``, ``Initializes``, and
refinement versions of these), and verifies the initialization of
variables. Proof verifies the absence of run-time errors and the
correctness of assertions such as ``Pre`` and ``Post`` aspects. Using the
switch ``--mode=<mode>``, whose possible values are ``check``,
``check_all``, ``flow``, ``prove`` ``all``, ``stone``, ``bronze``, ``silver``
and ``gold``, you can choose which analysis is performed:

* In mode ``check``, |GNATprove| partially checks that the program does not
  violate |SPARK| restrictions. The benefit of using this mode prior to mode
  ``check_all`` is that it is much faster, as it does not require the results
  of flow analysis.

* In mode ``check_all`` (``stone`` is a synonym for this mode), |GNATprove|
  fully checks that the program does not violate |SPARK| restrictions,
  including checks not performed in mode ``check`` like the absence of
  side-effects in functions. Mode ``check_all`` includes mode ``check``.

* In mode ``flow`` (``bronze`` is a synonym for this mode), |GNATprove| checks
  that no uninitialized data are read in the program, and that the specified
  data dependencies and flow dependencies are respected in the implementation.
  Mode ``flow`` includes mode ``check_all``.  This phase is called *flow
  analysis*.

* In mode ``prove`` ,
  |GNATprove| checks that the program is free from run-time errors, and that
  the specified functional contracts are respected in the implementation. Mode
  ``prove`` includes mode ``check_all``, as well as the part of mode ``flow``
  that checks that no uninitialized data are read, to guarantee soundness of
  the proof results. This phase is called *proof*.

* In the default mode ``all``, |GNATprove| does both flow analysis and proof.
  The ``silver`` and ``gold`` modes are synonyms for this mode.

Using the option ``--limit-line=`` one can limit proofs to a particular file
and line of an Ada file. For example, if you want to prove only line 12 of
file ``example.adb``, you can add the option ``--limit-line=example.adb:12`` to
the call to |GNATprove|. Using the option ``--limit-subp=`` one can limit proofs
to a subprogram declared in a particular file at a particular line.

A number of options exist to influence the behavior for proof. Internally, the
prover(s) specified with option ``--prover`` is/are called repeatedly for each
check or assertion. Using the option ``--timeout``, one can change the maximal
time that is allocated to each prover to prove each check or assertion.  Using
the option ``--steps`` (default: 100), one can set the maximum number of
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
proof levels, from the faster level 0 to the more powerful
level 4. More precisely, each value of ``--level`` is equivalent to directly
setting a collection of other switches discussed above:

* ``--level=0`` is equivalent to
  ``--prover=cvc4 --proof=per_check --timeout=1``
* ``--level=1`` is equivalent to
  ``--prover=cvc4,z3,altergo --proof=per_check --timeout=1``
* ``--level=2`` is equivalent to
  ``--prover=cvc4,z3,altergo --proof=per_check --timeout=5``
* ``--level=3`` is equivalent to
  ``--prover=cvc4,z3,altergo --proof=progressive --timeout=5``
* ``--level=4`` is equivalent to
  ``--prover=cvc4,z3,altergo --proof=progressive --timeout=10``

If both ``--level`` is set and an underlying switch is set (``--prover``,
``--timeout``, or ``--proof``), the value of the latter takes precedence over
the value set through ``--level``.

Note that using ``--level`` does not provide results that are reproducible
accross different machines. For nightly builds or shared repositories, consider
using the ``--steps`` or ``--replay`` switches instead. The number of steps
required to proved an example can be accessed by running |GNATprove| with the option
``--report=statistics``.

|GNATprove| also supports using the static analysis tool |CodePeer| as an
additional source for the proof of checks, by specifying the command line
option ``--codepeer=on`` (see :ref:`Using CodePeer Static Analysis`).

By default, |GNATprove| avoids reanalyzing unchanged files, on a
per-unit basis. This mechanism can be disabled with the option ``-f``.

When |GNATprove| proves a check, it stores this result in a session file,
along with the required time and steps for this check to be proved. This
information can be used to replay the proofs, to check that they are indeed
correct. When |GNATprove| is invoked using the ``--replay`` option,
it will attempt such a replay, using the same prover that was able to prove
the check last time, with some slightly higher time and step limit. In this
mode, the user-provided steps and time limits are ignored. If the ``--prover``
option is not provided, |GNATprove| will attempt to replay all checks,
otherwise it will replay only the proofs proved by one of the specified
provers.  If all
replays succeeded, |GNATprove| output will be exactly the same as a normal run
of |GNATprove|. If a replay failed, the corresponding check will be reported
as not proved. If a replay has not been attempted because the corresponding
prover is not available (a third-party prover that is not configured, or the
user has selected other provers using the ``--prover`` option), a warning will
be issued that the proof could not be replayed, but the check will still be
marked as proved.

By default, |GNATprove| stops at the first unit where it detect errors
(violations of Ada or |SPARK| legality rules). The option ``-k`` can be used to
get |GNATprove| to issue errors of the same kind for multiple units. If there
are any violations of Ada legality rules, |GNATprove| does not attempt any
analysis. If there are violations of |SPARK| legality rules, |GNATprove| stops
after the checking phase and does not attempt flow analysis or proof.

When an error is detected (which does not include issuing check messages),
|GNATprove| returns with a non-zero exit status. Otherwise, |GNATprove| returns
with an exit status of zero, even when warnings and check messages are issued.

Specifying the Run-Time Library and Target
------------------------------------------

The handling of runtimes of SPARK is now unified with that of the GNAT
compiler. See "GNAT User's Guide Supplement for Cross Platforms",
Section 3. If you specify a target, note that SPARK requires
additional configuration, see the next section.

.. _implementation_defined:

Specifying the Target Architecture and Implementation-Defined Behavior
----------------------------------------------------------------------

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

Note that specifying the ``Target`` attribute of project files is
not enough for |GNATprove|. In addition, you need to add the
following to your project file, under a scenario variable as seen in
:ref:`Having Different Switches for Compilation and Verification`:

.. code-block:: gpr

  project My_Project is
     [...]
     package Builder is
        case Mode is
           when "Compile" =>
              ...
           when "Analyze" =>
              for Global_Compilation_Switches ("Ada") use ("-gnateT=" & My_Project'Project_Dir & "/target.atp");
        end case;
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

Here is an example of a configuration file for a bare board PowerPC 750
processor configured as big-endian::

  Bits_BE                       1
  Bits_Per_Unit                 8
  Bits_Per_Word                32
  Bytes_BE                      1
  Char_Size                     8
  Double_Float_Alignment        0
  Double_Scalar_Alignment       0
  Double_Size                  64
  Float_Size                   32
  Float_Words_BE                1
  Int_Size                     32
  Long_Double_Size             64
  Long_Long_Size               64
  Long_Size                    32
  Maximum_Alignment            16
  Max_Unaligned_Field          64
  Pointer_Size                 32
  Short_Enums                   0
  Short_Size                   16
  Strict_Alignment              1
  System_Allocator_Alignment    8
  Wchar_T_Size                 32
  Words_BE                      1

  float          6  I  32  32
  double        15  I  64  64
  long double   15  I  64  64

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

.. _Using CodePeer Static Analysis:

Using CodePeer Static Analysis
------------------------------

.. note::

   |CodePeer| is only available as part of SPARK Pro 17 and beyond, but is not
   included in SPARK Discovery.

|CodePeer| is a static analysis tool developed and commercialized by AdaCore
(see http://www.adacore.com/codepeer). |GNATprove| supports using |CodePeer| as
an additional source for the proof of checks, by specifying the command line
option ``--codepeer=on``. |CodePeer| will be run before automatic provers. If
it proves a check, |GNATprove| will not attempt to run another prover on this
check.

When run by |GNATprove|, |CodePeer| does not attempt to generate preconditions,
and relies instead on user-provided preconditions for its analysis. |CodePeer|
analysis inside |GNATprove| is sound, in that it does not allow to prove a check
that could fail. |CodePeer| analysis may allow to prove more properties than
the strict contract-based reasoning performed in |SPARK| allow in general:

#. |CodePeer| generates a sound approximation of data dependencies for
   subprograms based on the implementation of subprograms and the call-graph
   relating subprograms. Hence |CodePeer| may be able to prove properties which
   cannot be deduced otherwise based on too coarse user-provided data
   dependencies.

#. |CodePeer| generates a sound approximation of loop invariants for
   loops. Hence |CodePeer| may be able to prove properties which cannot be
   deduced otherwise based on imprecise loop invariants, or in absence of a
   loop invariant.

In addition, |CodePeer| is using the same choice as GNAT compiler for the
rounding of fixed-point multiplication and division. This makes it more precise
for the analysis of code compiled with GNAT. If some code using fixed-point
arithmetic is compiled with another compiler than GNAT, and the code uses
fixed-point multiplication or division, the choice of rounding made in
|CodePeer| may not be suitable, in which case ``--codepeer=on`` should not be
used.

|CodePeer| analysis is particularly interesting when analyzing code using
floating-point computations, as |CodePeer| is both fast and precise for proving
bounds of floating-point operations.

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
:menuselection:`Edit --> Preferences` dialog in GPS, and opening
the :menuselection:`General --> Key Shortcuts` section.

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
changes its ``User profile`` for |SPARK| (in the |SPARK| section of the
Preferences dialog - menu :menuselection:`Edit --> Preferences`) from ``Basic``
to ``Advanced``, then a more complex panel is displayed for proof,
with more detailed switches.

|GNATprove| project switches can be edited from the panel ``GNATprove`` (menu
:menuselection:`Edit --> Project Properties`, in the :menuselection:`Build --> Switches`
section of the dialog).

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
   "float overflow check might fail",                      "VC_FP_OVERFLOW_CHECK"
   "range check might fail",                               "VC_RANGE_CHECK"
   "predicate check might fail",                           "VC_PREDICATE_CHECK"
   "predicate check might fail on default value",          "VC_PREDICATE_CHECK_ON_DEFAULT_VALUE"
   "invariant check might fail",                           "VC_INVARIANT_CHECK"
   "invariant check might fail on default value",          "VC_INVARIANT_CHECK_ON_DEFAULT_VALUE"
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
