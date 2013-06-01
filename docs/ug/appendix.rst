.. highlight:: ada

.. _Appendix:

********
Appendix
********

.. _command line:

Command-line Options
--------------------

|GNATprove| is executed with the following command line::

   gnatprove -P <project_file>.gpr <switches> <optional_list_of_files>

|GNATprove| accepts the following basic switches::

   -f            Force recompilation/proving of all units and all VCs
   -jnnn         Use nnn parallel processes (default: 1)
   --mode=       Proof mode
       check       Check SPARK restrictions for code where SPARK_Mode=On
       prove       Prove subprogram contracts and absence of run-time errors (default)
       flow        Prove object initialization, globals and depends contracts
       all         Activates all modes
   -q            Be quiet/terse
   --clean       Remove GNATprove intermediate files, and exit
   --report=     Output mode
       fail        Report failures to prove VCs (default)
       all         Report all results of proving VCs
       statistics  Report all results of proving VCs, including timing and
                   steps information
   -u            Unique compilation, only prove the given files
   -U            Prove all files of all projects
   -v, --verbose Output extra verbose information
   --version     Output version of the tool and exit
   -h, --help    Display usage information

|GNATprove| accepts the following advanced switches::

   -d, --debug            Debug mode
   --proof=               Proof mode
      no_wp                 Do not compute VCs, do not call prover
      all_split             Compute all VCs, save them to file, do not call prover
      path_wp               Generate one formula per path for each check
      no_split              Generate one formula per check
      then_split            Start with one formula per check, then split into paths when needed
   --pedantic             Use a strict interpretation of the Ada standard
   --steps=nnn            Set the maximum number of proof steps to nnn for Alt-Ergo
   --timeout=s            Set the prover timeout in seconds (default: 1)
   --limit-line=file:line Limit proofs to the specified file and line
   --limit-subp=file:line Limit proofs to the specified subprogram declared at
                          the location given by file and line
   --prover=s             Use given prover instead of default Alt-Ergo prover

.. _Project_Attributes:

Project Attributes
==================

|GNATprove| reads the package ``Prove`` in the given project file. This package
is allowed to contain an attribute ``Switches``, which defines additional
command line switches that are used for the invokation of |GNATprove|. As an
example, the following package in the project file sets the default mode of
|GNATprove| to ``prove``::

    package Prove is
       for Switches use ("--mode=prove");
    end Prove;

Switches given on the command line have priority over switches given in the
project file.

.. _GNATprove_Limitations:

|GNATprove| Limitations
=======================

|GNATprove| analyzes floating-point values and operations as if they were over
real numbers, with no rounding. The only rounding that occurs is for static
values (for example ``1.0``) which get rounded to their closest representable
floating-point value, depending on the type used in the code.

Using the option ``-gnatec=pragmas.adc`` as Default_Switch in a project file is
not supported. Instead, use ``for Local_Configuration_Pragmas use
"pragmas.adc";``.

Defining multiple units in the same file is not supported. Instead, define each
unit in a separate file.

Language Features Not Yet Supported
-----------------------------------

The major features not yet supported are:

* OO programming: tagged types, dispatching
* formal containers
* invariants on types (invariants and predicates)

|GNATprove| outputs in the :ref:`summary file` which features from |SPARK| are
not yet supported and used in the program [using brackets]:

* aggregate: aggregate extension;
* arithmetic operation: not yet implemented arithmetic operation;
* attribute: not yet implemented attribute;
* concatenation: array concatenation;
* container: formal container;
* dispatch: dispatching;
* expression with action: expression with action;
* multi dim array: multi-dimensional array of dimension > 4;
* pragma: not yet implemented pragma;
* representation clause: representation clause;
* tagged type: tagged type;
* type invariant;
* type predicate;
* operation on arrays: rarely used operation on arrays, such as boolean
  operators;
* iterators: loops with iterators;
* class wide types: class wide types;
* interfaces: interfaces;
* not yet implemented: any other not yet implemented construct.
