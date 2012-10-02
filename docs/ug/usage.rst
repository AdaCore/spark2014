Usage
=====

The GNATprove tool is packaged as an executable called "gnatprove". Like other
tools in GNAT Pro Toolsuite, GNATprove is based on the structure of GNAT
projects, defined in ``.gpr`` files.

Command-line Usage
------------------

GNATprove is executed with the following command line::

   gnatprove -P <project_file>.gpr <switches> <optional_list_of_files>

GNATprove accepts the following options::

   --mode=       Main mode
       detect      Detect and output Alfa information (default)
       force       Output errors for violations of Alfa (warn unimplemented)
       check       Check consistency of contracts
       prove       Prove subprogram contracts and absence of run-time errors

   --report=     Control reporting
       fail        Report failures to prove VCs (default)
       all         Report all results of proving VCs
       detailed    Report all results of proving VCs, including a reason when
                   not proved

   -u            Unique compilation, only prove the given files
   -U            Prove all files of all projects
   -q            Be quiet/terse
   -f            Fore recompilation/proving of all units and all VCs
   -jnnn         Use nnn parallel processes (default: 1)
   -v, --verbose Output extra verbose information

   --pedantic             Use a strict interpretation of the Ada standard
   --no-proof             Disable proof of VCs, only generate VCs
   --steps=nnn            Set the maximum number of proof steps to nnn for Alt-Ergo
   --timeout=s            Set the timeout for Alt-Ergo in seconds (default: 10)
   --help                 Display the list of options
   --limit-line=file:line Limit proofs to the specified file and line
   --limit-subp=file:line Limit proofs to the specified subprogram declared at
                          the location given by file and line

In modes ``detect`` and ``force``, GNATprove does not compute an accurate set
of global variables read and written in each subprogram. Hence, its detection
of subprograms in Alfa might be slightly more optimistic than the reality. When
using mode ``check`` or ``prove`` on the contrary, the detection is accurate.

Although ``--report`` has only some effect in modes ``check`` and ``prove``,
all combinations of options are allowed.

When given a list of files, GNATprove will consider them as entry points of
the program and prove these units and all units on which they depend. With
option ``-u``, the dependencies are not considered, only the given files
themselves are proved. With option ``-U``, all files of all projects are
proved.

With option ``--pedantic``, some compiler choices are forced to a worst-case
interpretation of the Ada standard. For example, ranges for integer base types
are reduced to the minimum guaranteed, not to the matching machine
integer type as done in practice on all compilers.

The options ``--steps`` and ``--timeout`` can be used to influence the behavior
of the prover Alt-Ergo. The option ``-j`` activates parallel compilation and
parallel proofs.  With the option ``--no-proof``, the prover is not actually
called, and gnatprove reports that it has skipped the VCs. With the option
``-q``, gnatprove does give the minimum of messages, while with option ``-v``,
on the contrary, all details are given.

Using the option ``--limit-line=`` one can limit proofs to a particular file
and line of an Ada file. For example, if you want to prove only the file 12 of
file ``example.adb``, you can add the option ``--limit-line=example.adb:12`` to
the call to GNATprove. Using the option ``--limit-subp=`` one can limit proofs
to a subprogram declared in a particular file at a particular line.

By default, gnatprove avoids recompiling/reproving unchanged files, on a
per-unit basis. This mechanism can be disabled with the option ``-f``.

Output
------

In mode ``detect``, GNATprove prints on the standard output warning messages
for Alfa subset violations, and information messages for unimplemented
features, as well as the :ref:`project statistics`. Detection information is
also to be found in the ``<name>.alfa`` files mentioned below.

In mode ``force``, GNATprove prints on the standard output error messages for
Alfa subset violations, and warning messages for unimplemented features.

In modes ``check`` or ``prove`` and report ``fail``, GNATprove prints on the
standard output error messages for unproved VCs.

In modes ``check`` or ``prove`` and report ``all``, GNATprove prints on the
standard output error messages for unproved VCs, and information messages for
proved VCs.

GNATprove always generates :ref:`project statistics` in file ``gnatprove.out``.

For each unit ``<name>``, GNATprove generates a :ref:`summary file`
``<name>.alfa`` in the sub-directory ``gnatprove`` of the corresponding
object directory.

Package in Project Files
------------------------

GNATprove reads the package ``Prove`` in the given project file. This package
is allowed to contain an attribute ``Switches``, which defines additional
command line switches that are used for the invokation of GNATprove. As an
example, the following package in the project file sets the default mode of
GNATprove to ``prove``::

    package Prove is
       for Switches use ("--mode=prove");
    end Prove;

Switches given on the command line have priority over switches given in the
project file.

Integration in GPS
------------------

GNATprove can be run from GPS. There is a menu ``Prove`` with the following
entries:

.. csv-table::
   :header: "Submenu", "Action"
   :widths: 1, 4

   "Prove All", "This runs GNATprove on all files in the project."
   "Prove Root Project", "This runs GNATprove on the entire project."
   "Prove File", "This runs GNATprove on the current unit."
   "Show Unprovable Code", "This runs GNATprove on the entire project in mode ``detect``."

When editing an Ada file, GNATprove can also be run from the context menu,
which can be obtained by a right click:

.. csv-table::
   :header: "Submenu", "Action"
   :widths: 1, 4

   "Prove File", "This runs GNATprove on the current unit."
   "Prove Line", "This runs proofs on the VCs of the current line of the current file."
   "Prove Subprogram", "This runs proofs on the VCs of the current subprogram whose declaration is pointed to."

GNATprove project switches can be edited from the panel ``GNATprove`` (in
``Project --> Edit Project Properties --> Switches``).

For unproved VCs, you can see in GPS a path for which gnatprove does not
manage to prove the VC. This can be achieved by right-clicking on the message
for the unproved VC in the location view, and choosing ``Prove --> Show
Path``.

We recommend that you enable the option ``Draw current line as a thin line``
(in ``Edit --> Preferences --> Editor --> Fonts & Colors``) so that GPS does not
hide the status of the checks on the current line (all proved in green /
otherwise in red). This is the default on recent versions of GPS.

Integration in GNATbench
------------------------

The current version is not integrated with GNATbench.

Known Limitations
-----------------

In modes ``check`` and ``prove``, the current version has the following
limitations:

   * It only accepts projects with a single object directory; it will stop
     with an error message if run on projects with more than one object
     directory.

   * It uses the location of the top-level instantiation for all VCs in
     instances of generics.

Using the option ``-gnatec=pragmas.adc`` as Default_Switch in a project file is
not supported. Instead, use ``for Local_Configuration_Pragmas use
"pragmas.adc";``.

Defining multiple units in the same file is not supported. Instead, define each
unit in a separate file.
