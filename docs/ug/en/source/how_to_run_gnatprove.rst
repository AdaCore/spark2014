How to Run GNATprove
====================

.. index:: project file; setup

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

Having Different Switches for Compilation and Verification
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In some cases, you may want to pass different compilation-level switches to
GNAT and |GNATprove|, for example use warning switches only for compilation, in
the same project file. In that case, you can use a scenario variable to specify
different switches for compilation and verification. We recommend to use the
predefined ``GPR_TOOL`` variable for this purpose:

.. code-block:: gpr

  project My_Project is

    Mode := External ("GPR_TOOL", "");

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

Running GNATprove from the Command Line
---------------------------------------

.. index::
    single: -U; all files in project
    single: -u

We recommend running |GNATprove| from the command line using a project file, as
follows::

    gnatprove -P <project-file.gpr>

In the appendix, section :ref:`Command Line Invocation`, you can find an
exhaustive list of switches; here we only give an overview over the most common
uses.

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

  All main units in the specified project and all units they (recursively)
  depend on are analyzed. If there are no main units specified, analyze all
  files in the project. Note that main units of projects that the specified
  project depends on are not taken into account.

  This is what you want to use for the analysis of a particular executable
  only, or if you want to analyze different executables within a complex
  project with different options.

* Analyze files::

     gnatprove -P <project-file.gpr> [-u] FILES...

  If ``-u`` is specified, we only analyze the units that contain the given
  files. If ``-u`` is not specified, we also analyze all units these units
  (recursively) depend on.

  This usage is intended for the day-to-day command-line or IDE use of
  |GNATprove| when implementing a project.

  Note that |GNATprove| always analyzes units as a whole, and cannot analyze a
  specification (``.ads``) file independently from a body (``.adb``) file. So
  if you specify a specification file that has a corresponding body, both are
  analyzed. The same is true for subunits such as separate subprograms: if you
  specify such a file name, the entire unit is analyzed.


.. index:: --mode
           Stone level; command-line switch
           Bronze level; command-line switch
           Silver level; command-line switch
           Gold level; command-line switch

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
  side effects in regular functions. Mode ``check_all`` includes mode
  ``check``.

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

.. index::
   single: --limit-line; command-line usage
   single: --limit-region
   single: --limit-lines

Using the option ``--limit-line`` one can limit proofs to a particular file
and line of an Ada file. For example, if you want to prove only line 12 of
file ``example.adb``, you can add the option ``--limit-line=example.adb:12`` to
the call to |GNATprove|. If a location is inside a generic, the file and line
can be prefixed by the file and line of the instantiation,
``--limit-line=example.adb:12:gen.adb:5``.

Using the option ``--limit-lines=file``, one can provide a file to |GNATprove|
where each line indicates a line to analyze. For example, such a file could
look like this::

   example.adb:12
   example.adb:15
   example.adb:18:gen.adb:5

Using ``--limit-region`` one can limit proofs to a range of lines in a
particular file. For example, ``--limit-region=example.adb:12:14`` will limit
analysis to lines 12 to 14 in ``example.adb``. Similar to ``--limit-line``, the
region can also be prefixed by an instantiation location:
``--limit-region=example.adb:8:gen.adb:12:14`` limits proof to lines 12 to 14
in ``gen.adb``, but only for the instance created at ``example.adb``, line 8.

.. index::
    single: --limit-subp
    single: --limit-name
    single: -U; analyze all instances

Using the ``--limit-name`` option, users can limit the analysis to subprograms
that have a specific name. Note that this option doesn't change the set of
units on which the analysis is run. For example, if a subprogram is outside of
the closure of the main program, it will not be analyzed even if the
``--limit-name`` option with the corresponding name is provided.

The ``--limit-name`` option cannot distinguish between multiple subprograms
that have the same name. Users can use the ``--limit-subp`` option, which
expects a location.  As an example, the option ``--limit-subp=example.ads:12``
limits the analysis to the subprogram declared at line 12 in ``example.ads``.
Note that ``--limit-subp`` implies analysis of the unit (``example.ads`` in the
example). If ``example.ads`` is a generic unit, SPARK skips analysis of such
units by default, as only instances of generics are analyzed. You can specify
the switch ``-U`` in this case to analyze all instances of the generic
subprogram.

One can specify a specific instance to analyze by specifying the place of
instantiation: the option ``--limit-subp=inst.adb:10:example.ads:12`` analyzes
the same subprogram, but only the instance that was created via the
instantiation at line 10 of ``inst.adb``. One can specify a longer chain if
``inst.adb`` is also part of a generic subprogram or package. In all cases, the
``-U`` switch is only needed if the first unit is a generic unit.

.. index:: --prover, --timeout, --memlimit, --steps, -j

A number of options exist to influence the behavior for proof. Internally, the
prover(s) specified with option ``--prover`` is/are called repeatedly for each
check or assertion. Using the options ``--timeout`` and ``--memlimit``, one
can change the maximal time and memory that is allocated to each prover to
prove each check or assertion.  Using the option ``--steps``,
one can set the maximum number of reasoning steps that the prover is allowed
to perform before giving up. The ``--steps`` option should be used when
repeatable results are required, because the results with a timeout and
memory limit may differ depending on the computing power, current load or
platform of the machine. A default value of 100 for ``--steps`` is used
if none of ``--steps`` or ``--timeout`` is used, either directly or
indirectly through ``--level``.

The option ``-j`` activates parallel compilation and
parallel proofs. With ``-jnnn``, at most nnn cores can be used in parallel.
With the special value ``-j0``, at most N cores can be used in parallel, when
N is the number of cores on the machine.

If more than one prover is specified via the ``--prover`` option, and without
parallel proofs enabled via the ``-j`` switch, the provers are tried in order
on each VC, until one of them succeeds or all fail. If parallel proofs are
enabled, provers might be run in parallel, and if one succeeds, the other
provers are interrupted. Interactive provers cannot be combined with other
provers, so must appear on their own.

.. index::
    single: -U; speeding up

.. note::

    When the project has a main file, or a file is passed as starting point to
    gnatprove, and the dependencies in the project are very linear (unit A
    depends only on unit B, which depends only on unit C, etc), then even when
    the ``-j`` switch is used, gnatprove may only consider one file at a time.
    This problem can be avoided by additionally using the ``-U`` switch.

.. note::

   The --memlimit switch is currently ineffective on the Mac OS X operating
   system, due to limitations of the underlying system call on that system.

.. index:: --proof

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

.. index:: --level

Instead of setting individually switches that influence the speed and power of
proof, one may use the switch ``--level``, which corresponds to predefined
proof levels, from the faster level 0 to the more powerful
level 4. More precisely, each value of ``--level`` is equivalent to directly
setting a collection of other switches discussed above:

* ``--level=0`` is equivalent to
  ``--prover=cvc5 --timeout=1 --memlimit=1000 --steps=0 --counterexamples=off``
* ``--level=1`` is equivalent to
  ``--prover=cvc5,z3,altergo --timeout=1 --memlimit=1000 --steps=0 --counterexamples=off``
* ``--level=2`` is equivalent to
  ``--prover=cvc5,z3,altergo --timeout=5 --memlimit=1000 --steps=0 --counterexamples=on``
* ``--level=3`` is equivalent to
  ``--prover=cvc5,z3,altergo --timeout=20 --memlimit=2000 --steps=0 --counterexamples=on``
* ``--level=4`` is equivalent to
  ``--prover=cvc5,z3,altergo --timeout=60 --memlimit=2000 --steps=0 --counterexamples=on``

If both ``--level`` is set and an underlying switch is set (``--prover``,
``--timeout``, ``--proof``, or ``--counterexamples``), the value of the latter
takes precedence over the value set through ``--level``.

Note that using ``--level`` does not provide results that are reproducible
accross different machines. For nightly builds or shared repositories, consider
using the ``--steps`` or ``--replay`` switches instead. The number of steps
required to proved an example can be accessed by running |GNATprove| with the option
``--report=statistics``.

.. index:: --proof-warnings

By default, |GNATprove| doesn't check for dead code in your subprograms nor does
it verify the logical consistency of subprogram contracts or assumptions. It is
thus possible to write a contract or assumption that is always false, which may
render subsequent analysis unsound, since False implies False is True. Contracts
or assumptions may be always false because they contain a contradiction (e.g.,
``X > 5 and X < 5``) or because their truth value is predetermined, e.g.:

.. code-block:: ada

  if X > 0 then
    ...

     pragma Assume (X < 0);

     ...
  end if;

|GNATprove| offers a switch, ``--proof-warnings=on``, that uses proof to help
identify unreachable branches and unreachable code and also to help identify
subprogram contracts or assumptions that are always false. These issues are
reported as warnings in |GNATprove|'s output.

.. note::

  The warnings issued by ``--proof-warnings=on`` are not guaranteed to
  be complete: an absence of warnings does not guarantee the logical
  consistenty of all subprogram contracts or assumptions; nor does it guarantee
  an absence of dead branches or code.

.. index:: -f

By default, |GNATprove| avoids reanalyzing unchanged files, on a
per-unit basis. This mechanism can be disabled with the option ``-f``.

.. index:: --replay

When |GNATprove| proves a check, it stores this result in a session file,
along with the required time and steps for this check to be proved. This
information can be used to replay the proofs, to check that they are indeed
correct. If such session files are present, and when |GNATprove| is invoked
using the ``--replay`` option, it will attempt such a replay, using the same
prover that was able to prove the check last time, with some slightly higher
time and step limit. In this mode, the user-provided steps and time limits are
ignored. If the ``--prover`` option is not provided, |GNATprove| will attempt
to replay all checks, otherwise it will replay only the proofs proved by one of
the specified provers.  If all replays succeeded, |GNATprove| output will be
exactly the same as a normal run of |GNATprove|. If a replay failed, the
corresponding check will be reported as not proved. If a replay has not been
attempted because the corresponding prover is not available (a third-party
prover that is not configured, or the user has selected other provers using the
``--prover`` option), a warning will be issued that the proof could not be
replayed, but the check will still be marked as proved.

.. index:: -k

By default, |GNATprove| stops at the first unit where it detect errors
(violations of Ada or |SPARK| legality rules). The option ``-k`` can be used to
get |GNATprove| to issue errors of the same kind for multiple units. If there
are any violations of Ada legality rules, |GNATprove| does not attempt any
analysis. If there are violations of |SPARK| legality rules, |GNATprove| stops
after the checking phase and does not attempt flow analysis or proof.

.. index:: --checks-as-errors
           --warnings; warnings as error

|GNATprove| returns with a non-zero exit status when an error is detected.
This includes cases where |GNATprove| issues unproved check messages when
switch ``--checks-as-errors=on`` is used, as well as cases where |GNATprove|
issues warnings when switch ``--warnings=error`` is used. In such cases,
|GNATprove| also issues a message about termination in error. Otherwise,
|GNATprove| returns with an exit status of zero, even when unproved check
messages and warnings are issued.

.. index:: project file; setting target and runtime
           Target
           Runtime

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
additional configuration, see the section :ref:`Specifying the Target
Architecture and Implementation-Defined Behavior`.

If you're using GNAT Common Code Generator to generate C code from SPARK, you
can specify the target and runtime as follows:

.. code-block:: gpr

   for Target use "c";
   for Runtime ("Ada") use "ccg";

As an alternative to these project file settings, you can also use the
command-line switches ``--RTS`` and ``--target`` to specify the target
and runtime.

.. index:: --pedantic

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

.. index:: -gnateT

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

.. index:: GNAT Studio integration

Running GNATprove from GNAT Studio
----------------------------------

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
   "Show Previous Runs",         "This displays previous runs of |GNATprove|."

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

The menu :menuselection:`SPARK --> Show Previous Runs` gives access to the
results of previous runs of |GNATprove| on the project, up to a bound which can
be set using the :menuselection:`Edit --> Preferences` dialog in GNAT Studio,
and opening the :menuselection:`Plugins --> Gnatprove Runs` section. Note that
the higher this bound, the more disk space will be used to store the results of
previous runs of |GNATprove|.

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
   "Globals",                "This generates Global contracts for the current file."

Except from :menuselection:`Examine File`, :menuselection:`Prove File`, and
:menuselection:`Globals`, all other submenus are also applicable to code inside
generic units, in which case the corresponding action is applied to all
instances of the generic unit in the project. For example, if a generic unit is
instantiated twice, selecting :menuselection:`Prove Subprogram` on a subprogram
inside the generic unit will apply proof to the two corresponding subprograms
in instances of the generic unit.

.. index:: pair: Stone level; GNAT Studio integration
           pair: Bronze level; GNAT Studio integration

The menus :menuselection:`SPARK --> Examine ...` open a panel which allows
setting various switches for |GNATprove|'s analysis. The main choice offered in
this panel is to select the mode of analysis, among modes ``check``,
``check_all`` (which corresponds to the ``stone`` analysis mode) and ``flow``
(the default, which corresponds to the ``bronze`` analysis mode).

.. index:: pair: Silver level; GNAT Studio integration
           pair: Gold level; GNAT Studio integration

The menus :menuselection:`SPARK --> Prove ...` open a panel which allows
setting various switches for |GNATprove|'s analysis, corresponding to the
``silver`` and ``gold`` analysis modes. By default, this panel offers a few
simple choices, like the proof level (see description of switch ``--level`` in
:ref:`Running GNATprove from the Command Line`). If the user changes its ``User
profile`` for |SPARK| (in the |SPARK| section of the Preferences dialog - menu
:menuselection:`Edit --> Preferences`) from ``Basic`` to ``Advanced``, then a
more complex panel is displayed for proof, with more detailed switches.

|GNATprove| project switches can be edited from the panel ``GNATprove`` (menu
:menuselection:`Edit --> Project Properties`, in the :menuselection:`Build --> Switches`
section of the dialog).

When proving a check fails on a specific path through a subprogram (for both
checks verified in flow analysis and in proof), |GNATprove| may generate path
information for the user to see. The user can display this path in GNAT Studio by
clicking on the icon to the left of the failed proof message, or to the left of
the corresponding line in the editor. The path is hidden again when re-clicking
on the same icon.

The contextual menu :menuselection:`SPARK --> Globals --> ...` allows the user
to show and hide the Global contracts that are internally generated by
|GNATprove| for the current unit. This can be useful when learning how to write
:ref:`Data Dependencies`, because the tool provides the contracts where they
are missing.  Note that this does not modify the unit source code - the Global
contracts are inserted into a special buffer; the buffer contents can be
copy-pasted into the editor if desired.

.. index:: pair: counterexample; GNAT Studio integration

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

.. index:: Visual Studio Code

Running GNATprove from Visual Studio Code
-----------------------------------------

|GNATprove| can be run from Visual Studio Code, using the `Ada/SPARK extension
for Visual Studio Code
<https://marketplace.visualstudio.com/items?itemName=AdaCore.ada>`_.  It
provides the following "auto-detected" tasks (under menu
:menuselection:`Terminal --> Run Task...`):

.. csv-table::
   :header: "Submenu", "Action"
   :widths: 1, 4

   "Examine project",        "This runs |GNATprove| in flow analysis mode on all mains and the units they depend on in the project."
   "Examine file",           "This runs |GNATprove| in flow analysis mode on the current unit, its body and any subunits."
   "Examine subprogram",     "This runs |GNATprove| in flow analysis mode on the current subprogram."
   "Prove project",          "This runs |GNATprove| on all mains and the units they depend on in the project."
   "Prove file",             "This runs |GNATprove| on the current unit, its body and any subunits."
   "Prove subprogram",       "This runs |GNATprove| on the current subprogram."
   "Prove selected region",  "This runs |GNATprove| on the currently selected region."
   "Prove line",             "This runs |GNATprove| on the current line."

.. index:: GNATbench

Running GNATprove from GNATbench
--------------------------------

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
   "Globals",            "This generates Global contracts for the current file."

.. index:: manual proof
           Platinum level; manual proof

Running GNATprove Without a Project File
----------------------------------------

|GNATprove| accepts the invocation without a project file (``-P`` switch on the
command line). In that case, if the current directory contains exactly one
project file, |GNATprove| uses this project file.  If no project file exists,
|GNATprove| creates a trivial project file with the name ``default.gpr`` and
uses that.

GNATprove and Manual Proof
--------------------------

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

.. index:: --limit-line; calling an interactive prover

Analysis with |GNATprove| can be limited to a single condition with the
``--limit-line`` option::

    gnatprove -P <project-file.gpr> --prover=<prover> --limit-line=<file>:<line>:<column>:<check-kind>

Please use the output of ``gnatprove --list-categories`` to determine the
``check-kind`` to be provided in this command.

.. index:: pair: manual proof; GNAT Studio integration

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

.. index:: pair: -j; speeding up

* Use the ``-j`` switch to use more than one core on your machine. |GNATprove|
  can make efficient usage of multi-processing. If your machine has more than
  one processor or core, we strongly suggest to enable multi-processing, using
  the ``-j`` switch. This switch should not have an impact on proof results,
  only on running time.

.. index:: pair: --no-loop-unrolling; speeding up

* Use ``--no-loop-unrolling`` to deactivate loop unrolling. Loop unrolling can
  often avoid the use of a loop invariant, but it almost always will be more
  costly to analyze than a loop with a loop invariant. See also :ref:`Automatic
  Unrolling of Simple For-Loops`.

.. index:: pair: --no-inlining; speeding up

* Use ``--no-inlining`` to deactivate contextual analysis of local subprograms
  without contracts. This feature can often avoid the use of subprogram
  contracts, but it will be more costly to analyze such subprograms in their
  calling context than analyzing them separately. See also :ref:`Contextual
  Analysis of Subprograms Without Contracts`.

.. index:: pair: --counterexamples; speeding up

* Use ``--counterexamples=off`` to deactive counterexamples. Counter-examples
  are very useful to understand the reason for a failed proof attempt. You can
  disable this feature if you are not working on a failed proof attempt.

.. index:: pair: --level; speeding up

* Use the ``--level`` switch to use a lower level and faster preset.
  Generally, a lower level is faster than higher levels. See also :ref:`Running
  GNATprove from the Command Line`.

.. index:: pair: --prover; speeding up
           pair: --timeout; speeding up
           pair: --steps; speeding up

* More fine-grained than the ``--level`` switch, you can directly set the
  ``--prover``, ``--timeout`` and ``--steps`` options. Using only one prover
  with a small timeout or a small steps limit will result in much faster
  execution.

.. index:: pair: --replay; speeding up

* If you have access to up-to-date session files, (see
  :ref:`Running GNATprove from the Command Line`) and you only want to check
  the proof results of the stored session, you can use ``--replay``. Replay
  only runs previously successful provers and is therefore much faster than a
  run of |GNATprove| without this option.

.. index:: pair: --function-sandboxing; speeding up

* Use ``--function-sandboxing=off``. By default, |GNATprove| sandboxes functions
  to limit the impact of :ref:`Infeasible Subprogram Contracts`. These guards
  have a non-negligible impact on prover performance. If
  in your project, all subprograms are in the |SPARK| subset, or you have
  confidence in the contracts you wrote for the subprograms which are not in
  |SPARK|, you can disable these guards using the ``--function-sandboxing=off``
  option.

* Use ``--memcached-server`` switch for :ref:`Sharing Proof Results Via a
  Cache`.

|GNATprove| and Network File Systems or Shared Folders
------------------------------------------------------

On Linux and Mac-OS, |GNATprove| needs to create a Unix domain socket file.
This might be a problem if |GNATprove| attempts to create such a file in a
directory that is a shared folder or on a network file system like NFS, which
does not support such folders. To minimize chances for this to occur,
|GNATprove| determines the folder to create that special file as follows:

* if the environment variable ``TMPDIR`` is set, and the corresponding directory
  exists and is writeable, use that; otherwise,
* if ``/tmp`` exists and is writable, use that; otherwise,
* use the ``gnatprove`` subfolder of the object directory of the root project.

On Linux, |GNATprove| uses POSIX semaphores to coordinate parallel processes.
If your system does not provide POSIX semaphores (this may be the case in some
virtualized environments), |GNATprove| fails with a message similar to the
following::

  failed to create semaphore: Permission denied

In this case, you can use the switch `--debug-no-semaphore` to avoid the use of
semaphores. This switch might reduce the performance of the tool in some cases,
but otherwise should not affect its behavior.
