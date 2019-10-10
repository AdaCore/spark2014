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

Note that you can use the project wizard from GNAT Studio to create a project file
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
different switches for compilation and verification. We recommend to use the
predefined ``GPR_TOOL`` variable for this purpose:

.. code-block:: gpr

  project My_Project is

    Mode := External ("GPR_TOOL");

    package Compiler is
       case Mode is
          when "gnatprove" =>
             for Switches ("Ada") use ...
          when others =>
             for Switches ("Ada") use ...
       end case;
    end Compiler;

  end My_Project;

With the above project, compilation will be automatically done in the "normal"
mode (the "others" branch above)::

  gprbuild -P my_project.gpr

while |GNATprove| automatically sets the ``GPR_TOOL`` variable to the ``gnatprove`` value::

  gnatprove -P my_project.gpr

Other tools set the value of this variable to other values. See the
documentation of other AdaCore tools to know more about this.

Note that before SPARK Pro 20, the ``GPR_TOOL`` was not set automatically by the
tool. You can set it manually in this case::

  gnatprove -P my_project.gpr -XGPR_TOOL=gnatprove

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
to a subprogram declared in a particular file at a particular line. Using
``--limit-region=`` one can limit proofs to a range of lines in a particular
file. For example, ``--limit-region=example.adb:12:14`` will limit analysis to
lines 12 to 14 in ``example.adb``.

A number of options exist to influence the behavior for proof. Internally, the
prover(s) specified with option ``--prover`` is/are called repeatedly for each
check or assertion. Using the options ``--timeout`` and ``--memlimit``, one
can change the maximal time and memory that is allocated to each prover to
prove each check or assertion.  Using the option ``--steps`` (default: 100),
one can set the maximum number of reasoning steps that the prover is allowed
to perform before giving up. The ``steps`` option should be used when
predictable results are required, because the results with a timeout and
memory limit may differ depending on the computing power, current load or
platform of the machine. The option ``-j`` activates parallel compilation and
parallel proofs. With ``-jnnn``, at most nnn cores can be used in parallel.
With the special value ``-j0``, at most N cores can be used in parallel, when
N is the number of cores on the machine.

.. note::

    When the project has a main file, or a file is passed as starting point to
    gnatprove, and the dependencies in the project are very linear (unit A
    depends only on unit B, which depends only on unit C, etc), then even when
    the ``-j`` switch is used, gnatprove may only consider one file at a time.
    This problem can be avoided by additionally using the ``-U`` switch.

.. note::

   The --memlimit switch is currently ineffective on the Mac OS X operating
   system, due to limitations of the underlying system call on that system.

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
  ``--prover=cvc4 --timeout=1 --memlimit=1000 --steps=0``
* ``--level=1`` is equivalent to
  ``--prover=cvc4,z3,altergo --timeout=1 --memlimit=1000 --steps=0``
* ``--level=2`` is equivalent to
  ``--prover=cvc4,z3,altergo --timeout=5 --memlimit=1000 --steps=0``
* ``--level=3`` is equivalent to
  ``--prover=cvc4,z3,altergo --timeout=20 --memlimit=2000 --steps=0``
* ``--level=4`` is equivalent to
  ``--prover=cvc4,z3,altergo --timeout=60 --memlimit=2000 --steps=0``

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

|GNATprove| returns with a non-zero exit status when an error is detected.
This includes cases where |GNATprove| issues unproved check messages when
switch ``--checks-as-errors`` is used, as well as cases where |GNATprove|
issues warnings when switch ``--warnings=error`` is used. In such cases,
|GNATprove| also issues a message about termination in error. Otherwise,
|GNATprove| returns with an exit status of zero, even when unproved check
messages and warnings are issued.

Using the GNAT Target Runtime Directory
---------------------------------------

If you are using GNAT as your target compiler and explicitly specify
a runtime and target to use in your project, for instance:

.. code-block:: gpr

   for Target use "arm-eabi";
   for Runtime ("Ada") use "ravenscar-sfp-stm32f4";

|GNATprove| will take such setting into account and will use the GNAT
runtime directory, as long as your target compiler is found in your PATH
environment variable. Note that you will need to use a matching version
of GNAT and |SPARK| (e.g. GNAT 18.2 and SPARK 18.2).

The handling of runtimes of |GNATprove| is in fact unified with that of the
GNAT compiler. For details, see "GNAT User's Guide Supplement for Cross
Platforms", Section 3. If you specify a target, note that |GNATprove| requires
additional configuration, see the section :ref:`implementation_defined`.

If you're using GNAT Common Code Generator to generate C code from SPARK, you
can specify the target and runtime as follows:

.. code-block:: gpr

   for Target use "c";
   for Runtime ("Ada") use "ccg";

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

If you specify the ``Target`` and ``Runtime`` attributes in your project file
or via the ``--target`` and ``--RTS`` switches, |GNATprove| attempts to
configure automatically the target dependent values such as endianness or sizes
and alignments of standard types. If this automatic configuration fails,
|GNATprove| outputs a warning and assumes that the compilation target is the
same as the host on which it is run.

You can however configure the target dependent values manually. In addition to
specifying the target and runtime via the project file or the commandline, you
need to add the following to your project file, under a scenario variable as
seen in :ref:`Having Different Switches for Compilation and Verification`:

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
  cross-compilation is used. If |GNAT Pro| is the cross compiler and the
  automatic configuration fails, the configuration file can be generated by
  calling the compiler for your target with the switch ``-gnatet=target.atp``.
  Otherwise, the target file should be generated manually.
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

.. _Using CodePeer Static Analysis:

Using CodePeer Static Analysis
------------------------------

.. note::

   |Codepeer| is only available in SPARK Pro. It is not available in the
   following SPARK releases:

   - the Community release
   - SPARK Discovery
   - on the MacOS X operating system

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
#. |CodePeer| ignores the ``SPARK_Mode`` pragma and aspects; in particular it
   uses information that is hidden from SPARK using ``pragma SPARK_Mode(Off)``
   or the equivalent aspect.

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

.. _Running GNATprove from GNAT Studio:

Running |GNATprove| from GNAT Studio
------------------------------------

|GNATprove| can be run from GNAT Studio. When |GNATprove| is installed and found on
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
:menuselection:`Edit --> Preferences` dialog in GNAT Studio, and opening
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

   "Examine File",           "This runs |GNATprove| in flow analysis mode on the current unit, its body and any subunits."
   "Examine Subprogram",     "This runs |GNATprove| in flow analysis mode on the current subprogram."
   "Prove File",             "This runs |GNATprove| on the current unit, its body and any subunits."
   "Prove Subprogram",       "This runs |GNATprove| on the current subprogram."
   "Prove Line",             "This runs |GNATprove| on the current line."
   "Prove Selected Region",  "This runs |GNATprove| on the currently selected region."
   "Prove Check",            "This runs |GNATprove| on the current failing condition. |GNATprove| must have been run at least once for this option to be available in order to know which conditions are failing."

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
information for the user to see. The user can display this path in GNAT Studio by
clicking on the icon to the left of the failed proof message, or to the left of
the corresponding line in the editor. The path is hidden again when re-clicking
on the same icon.

For checks verified in proof, |GNATprove| may also generate counterexample
information for the user to see (see :ref:`Understanding Counterexamples`). The
user can display this counterexample in GNAT Studio by clicking on the icon to the left
of the failed proof message, or to the left of the corresponding line in the
editor. The counterexample is hidden again when re-clicking on the same icon.

A monospace font with ligature like Fira Code
(https://github.com/tonsky/FiraCode) or Hasklig
(https://github.com/i-tu/Hasklig) can be separately installed and selected to
make contracts more readable inside GNAT Studio or GNATbench. See the following
screenshot which shows how symbols like :code:`=>` (arrow) or :code:`>=`
(greater than or equal) are displayed in such a font:

.. image:: /static/firacode.png

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
may be proved using manual proof inside GNAT Studio or an external interactive prover.

In the appendix, section :ref:`Alternative_Provers`, is explained how to use
different provers than the one |GNATprove| uses as default.

Calling an Interactive Prover From the Command Line
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

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

Please use the output of ``gnatprove --list-categories`` to determine the
``check-kind`` to be provided in this command.

Calling an Interactive Prover From GNAT Studio
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

After running |GNATprove| with proof mode, the menu
:menuselection:`SPARK --> Prove Check` is available by right-clicking on a
check message in the location tab or by right-clicking on a line that fails
because of a single condition (i.e. there is only one check in the output of
|GNATprove| concerning this line).

In the dialog box, the field "Alternate prover" can be filled to use another
prover than Alt-Ergo. If the alternative prover is configured as
"interactive", after the execution of :menuselection:`SPARK --> Prove Check`,
GNAT Studio opens the manual proof file with the editor corresponding to the prover
under the condition that an editor is specified in the configuration of the
alternative prover.

Once the editor is closed, GNAT Studio re-executes
:menuselection:`SPARK --> Prove Check`. The user should verify the same
alternative prover as before is still specified. After execution, GNAT Studio will
offer to re-edit the file if the proof fails.


Manual Proof Within GNAT Studio
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A manual proof system is integrated into GNAT Studio. It allows the user to directly
visualize the verification condition, apply simple proof steps on it, and call
provers to discharge it. The proof system is available after running
|GNATprove| via one of the ``Prove ...`` menus. By right-clicking on a check
message in the location tab, and selecting the menu :menuselection:`SPARK -->
Start Manual Proof` the proof system starts. It consists of the Manual Proof
console, the Proof Tree and the current Verification Condition being dealt
with.

The user interacts with the system mainly using the manual proof console. Three
types of commands can be entered:

 * Some helper commands such as ``help``, ``list-provers`` and
   ``list-transforms`` are available.
 * When a prover name (type ``list-provers`` to see a list of the available
   provers) is entered, the corresponding prover is run on the verification
   condition that is selected in the proof tree.
 * A transformation (see ``list-transforms`` and the below table for the
   available transformations) can modify the proof tree. A transformation
   applies to a verification condition or goal and may produce several new
   subgoals. For example, the transformation ``assert`` allows the user to
   assert an auxiliary fact. This transformation will create two subgoals, one
   to prove the assertion, and the other to prove that the assertion implies
   the previous goal.

The Manual proof system can be quit by selecting :menuselection:`SPARK --> Exit
Manual Proof` in the menu. A pop-up window asks if the user wants to save the
session. It is recommended to close it using the menu because it makes sure to
close everything related to manual proof. A tutorial to the proof system can be
found in :ref:`Manual Proof Using GNAT Studio`.

List of Useful Transformations and Commands for Manual Proof
""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""

The transformations all contain a specific documentation through the
``list-transforms`` command and ``help transform_name`` command. The most
useful transformations/commands are the following:

* ``apply``: apply an hypothesis to the current goal.
  For example: ``H : x > 0 -> not x = 0`` can be applied on the goal
  ``G : not x = 0``. After the application you will be left to prove a new goal
  ``x > 0``.

* ``assert``: adds a new lemma you can use for proving the current Verification
  Condition.
  For example: ``assert x = 0`` will generate two new subgoals. In the first
  one you have to prove that x is indeed equal to 0. In the second one, you can
  use this hypothesis.

* ``case``: takes a formula and perform an analysis by case on its boolean
  value. You will have to prove your Verification Condition once with this
  formula asserted to true and once asserted to false.

* ``clean``: removes unsuccessful proof attempts below proved goals.

* ``clear_but``: removes all hypotheses except the one provided by the user as
  argument. Removing unused context helps the provers.
  For example, ``clear_but H,H2,h`` will remove everything but hypotheses H H2
  and h.

* ``compute_in_goal``: performs possible computations in goal.

* ``destruct``: destruct the head constructor of a formula ( ``/\`` , ``\/``
  or ``->``).
  With ``H: A /\ B``, applying ``destruct H`` make two new hypotheses (``H: A``
  and ``H1: B``). With ``H: A \/ B``, applying ``destruct H`` duplicates the
  goal which has to be proved with ``H: A`` and ``H: B`` independently. With
  ``H: A -> B``, ``destruct H`` creates a new subgoal for ``A`` and simplify to
  ``H: B`` in the current one.

* ``eliminate_epsilon``: sometimes the goal appears as ``epsilon [...]``. This
  transforms epsilons into adapted logic.

* ``exists``: allows the user to provide a term that instantiates a goal
  starting with an existential.

* ``help``: with no arguments, return basic commands that can be used. If a
  transformation is given as argument, it displays a small description of the
  transformation.

* ``induction``: performs an induction on the unbounded integer specified.

* ``instantiate``: instantiates a ``forall`` quantification at the head of an
  hypothesis with a term given by the user (a list of terms can be provided).

* ``intros``: introduces a list of constants/hypotheses. This transformation
  should not be necessary but it can be used to rename constants/hypotheses.

* ``left``: In a goal, transforms ``A \/ B`` into ``A``.

* ``list-provers``: gives a list of the provers available on your machine. You
  should have at least ``altergo``.

* ``list-transforms``: list transformations.

* ``pose``: defines a new constant equal to a given term.

* ``print``: prints the definition of a name.

* ``remove``: removes a list of hypotheses.

* ``replace``: replace a term by another and create a subgoal asking the user
  to show that they are equivalent.

* ``rewrite``: rewrites an equality in a goal or hypothesis. For example, with
  ``H: x = 0`` and goal ``y = x``, ``rewrite H`` transforms the goal into
  ``y = 0``.

* ``right``: In a goal, transforms ``A \/ B`` into ``B``.

* ``search``: search all occurrences of a name in the context.

* ``split_*``: a set of transformations that split the goals/hypotheses. For
  example, ``split_goal_wp`` transforms the goal ``A /\ B`` into two new
  subgoals ``A`` and ``B``.

* ``subst``: try to find an equality that could be used for a given constant and
  replace each occurrence of this constant by the other side of the equality. It
  then removes said constant.

* ``subst_all``: do all possible substitutions.

* ``unfold``: unfolds the definition of a function in an hypothesis or a goal.

Recommendations and Tips for Manual Proof
"""""""""""""""""""""""""""""""""""""""""

* As for proofs with an external interactive prover, the user should set the
  attribute ``Proof_Dir`` so that proofs can be saved under version control.

* The ``Proof_Dir`` is recommended to be under a version control system (git or
  svn for example). The proofs can be tedious to rewrite so it is better not to
  lose them.

* There is currently no way to adapt proofs made on a given version of the code
  when the code is changed. The update will have to be done manually but
  we hope to automate the process in the future.

* This feature is experimental and we currently recommend to keep the proof as
  short as possible.

* If the goal contains epsilons, they can be removed by using
  ``eliminate_epsilon``.

* Manual provers can be launched during the edition of the proof like
  other provers. The user can select a goal node and type ``coq`` for example.

* The command line remembers what is typed. Arrow keys can be used to get the
  lasts queried commands.

How to Speed Up a Run of |GNATprove|
------------------------------------

|GNATprove| can take some time on large programs with difficult checks to
prove. This section describes how one can improve the running time of the
|GNATprove| tool. Note that some of the suggested settings will decrease the
number of proved checks or decrease usability of the tool, because spending
more time often results in more successful proofs. You may still want to try
some of the suggestions here to see if the time spent by |GNATprove| is really
useful in your context.

These settings will speed up |GNATprove|:

* Use the ``-j`` switch to use more than one core on your machine. |GNATprove|
  can make efficient usage of multi-processing. If your machine has more than
  one processor or core, we strongly suggest to enable multi-processing, using
  the ``-j`` switch. This switch should not have an impact on proof results,
  only on running time.

* Use ``--no-loop-unrolling`` to deactivate loop unrolling. Loop unrolling can
  often avoid the use of a loop invariant, but it almost always will be more
  costly to analyze than a loop with a loop invariant. See also :ref:`Automatic
  Unrolling of Simple For-Loops`.

* Use ``--no-inlining`` to deactivate contextual analysis of local subprograms
  without contracts. This feature can often avoid the use of subprogram
  contracts, but it will be more costly to analyze such subprograms in their
  calling context than analyzing them separately. See also :ref:`Contextual
  Analysis of Subprograms Without Contracts`.

* Use ``--no-counterexample`` to deactive counterexamples. Counter-examples are
  very useful to understand the reason for a failed proof attempt. You can
  disable this feature if you are not working on a failed proof attempt.

* Use the ``--level`` switch to use a lower level and faster presets.
  Generally, a lower level is faster than higher levels. See also :ref:`Running
  GNATprove from the Command Line`.

* More fine-grained than the ``--level`` switch, you can directly set the
  ``--prover``, ``--timeout`` and ``--steps`` options. Using only one prover
  with a small timeout or a small steps limit will result in much faster
  execution.

|GNATprove| and Network File Systems or Shared Folders
------------------------------------------------------

On Linux and Mac-OS, |GNATprove| needs to create a Unix domain socket file.
This might be a problem if |GNATprove| attempts to create such a file in a
directory that is a shared folder or on a network file system like NFS, which
does not support such folders. To minimize changes for this to occur,
|GNATprove| determines the folder to create that special file as follows:

* if the environment variable ``TMPDIR`` is set, and the corresponding directory
  exists and is writeable, use that; otherwise,
* if ``/tmp`` exists and is writable, use that; otherwise,
* use the ``gnatprove`` subfolder of the object directory of the root project.
