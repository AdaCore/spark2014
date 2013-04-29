.. _formal verification with gnatprove:

Formal Verification with |GNATprove|
====================================

The |GNATprove| tool is packaged as an executable called ``gnatprove``. Like
other tools in |GNAT Pro| Toolsuite, |GNATprove| is based on the structure of
GNAT projects, defined in ``.gpr`` files.

.. _command line:

Command-line Usage
------------------

|GNATprove| is executed with the following command line::

   gnatprove -P <project_file>.gpr <switches> <optional_list_of_files>

|GNATprove| accepts the following basic switches::

   -f            Force recompilation/proving of all units and all VCs
   -jnnn         Use nnn parallel processes (default: 1)
   --mode=       Proof mode
       detect      Detect and output SPARK information
       force       Output errors for violations of SPARK (warn unimplemented)
       prove       Prove subprogram contracts and absence of run-time errors (default)
       flow        Prove object initialization and globals and depends contracts
       all         Both analyses flow and prove are activated
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
      path_wp               Use traditional way of computing VCs, one for each path
      no_split              Compute one VC per check
      then_split            Start with one VC per check, then split
   --pedantic             Use a strict interpretation of the Ada standard
   --steps=nnn            Set the maximum number of proof steps to nnn for Alt-Ergo
   --timeout=s            Set the prover timeout in seconds (default: 1)
   --limit-line=file:line Limit proofs to the specified file and line
   --limit-subp=file:line Limit proofs to the specified subprogram declared at
                          the location given by file and line
   --prover=s             Use given prover instead of default Alt-Ergo prover

In modes ``detect`` and ``force``, |GNATprove| does not compute an accurate set
of global variables read and written in each subprogram. Hence, its detection
of subprograms in |SPARK| might be slightly more optimistic than the
reality. When using mode ``prove``, ``flow`` or ``all`` on the contrary, the
detection is accurate.

Although ``--report`` has only some effect in modes ``prove`` and ``all``, all
combinations of options are allowed.

When given a list of files, |GNATprove| will consider them as entry points of
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
parallel proofs.  The option ``proof`` is intended for debug use and influences
the work that is actually done by |GNATprove|. If this option is set to
``no_split`` (default unless ``--limit-line`` is used), one VC is generated for
each check, which will make |GNATprove| run faster, and avoid any possible
combinatorial explosion of the number of VCs. If this option is set to
``then_split`` (default when ``--limit-line`` is used), |GNATprove| will start
by computing a single VC for each check like for ``no_split``, but then each
unproved VC is splitted if possible, which is slower but more precise. If this
option is set to ``no_wp``, the VCs are not computed, and no prover is
called. If this option is set to ``all_split`` the VCs are computed, but no
prover is called. If this option is set to ``path_wp``, one VC is generated for
each path. With the option ``-q``, |GNATprove| does give the minimum of
messages, while with option ``-v``, on the contrary, all details are given.

Using the option ``--limit-line=`` one can limit proofs to a particular file
and line of an Ada file. For example, if you want to prove only the file 12 of
file ``example.adb``, you can add the option ``--limit-line=example.adb:12`` to
the call to |GNATprove|. Using the option ``--limit-subp=`` one can limit proofs
to a subprogram declared in a particular file at a particular line.

By default, |GNATprove| avoids recompiling/reproving unchanged files, on a
per-unit basis. This mechanism can be disabled with the option ``-f``.

Output
------

In mode ``detect``, |GNATprove| prints on the standard output warning messages
for |SPARK| subset violations, and information messages for unimplemented
features, as well as the :ref:`project statistics`. Detection information is
also to be found in the ``<name>.alfa`` files mentioned below.

In mode ``force``, |GNATprove| prints on the standard output error messages for
|SPARK| subset violations, and warning messages for unimplemented features.

In mode ``prove`` and report ``fail``, |GNATprove| prints on the standard
output error messages for unproved VCs.

In mode ``prove`` and report ``all`` or ``statistics``, |GNATprove| prints on
the standard output error messages for unproved VCs, and information messages
for proved VCs.

In mode ``flow``, GNATprove prints on the standard output error messages and
warnings for incorrect Globals and depends contracts, unitialized error
messages, and suspicious situations such as unused assignments, missing return
statements and so on.

In mode ``all``, GNATprove behaves just as if both modes ``prove`` and
``flow`` were activated.

|GNATprove| always generates :ref:`project statistics` in file
``gnatprove.out``.

For each unit ``<name>``, |GNATprove| generates a :ref:`summary file`
``<name>.alfa`` in the sub-directory ``gnatprove`` of the corresponding
object directory.

Package in Project Files
------------------------

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

.. _GPS integration:

Integration in GPS
------------------

|GNATprove| can be run from GPS. There is a menu ``Prove`` with the following
entries:

.. csv-table::
   :header: "Submenu", "Action"
   :widths: 1, 4

   "Prove All", "This runs |GNATprove| on all files in the project."
   "Prove Root Project", "This runs |GNATprove| on the entire project."
   "Prove File", "This runs |GNATprove| on the current unit."
   "Show Unprovable Code", "This runs |GNATprove| on the entire project in mode ``detect``."

When editing an Ada file, |GNATprove| can also be run from the context menu,
which can be obtained by a right click:

.. csv-table::
   :header: "Submenu", "Action"
   :widths: 1, 4

   "Prove File", "This runs |GNATprove| on the current unit."
   "Prove Line", "This runs proofs on the VCs of the current line of the current file."
   "Prove Subprogram", "This runs proofs on the VCs of the current subprogram whose declaration is pointed to."

|GNATprove| project switches can be edited from the panel ``GNATprove`` (in
``Project --> Edit Project Properties --> Switches``).

In some proof modes (``--proof=then_split`` or ``--proof=path_wp``),
|GNATprove| attempts to prove checks separately for the possible paths leading
to a check. If the proof fails on a specific path, the user can display this
path in GPS by clicking on the icon to the left of the failed proof message, or
to the left of the corresponding line in the editor. The path is hidden again
when re-clicking on the same icon.

We recommend that you enable the option ``Draw current line as a thin line``
(in ``Edit --> Preferences --> Editor --> Fonts & Colors``) so that GPS does not
hide the status of the checks on the current line (all proved in green /
otherwise in red). This is the default on recent versions of GPS.

Integration in GNATbench
------------------------

The current version is not integrated with GNATbench.

Recommended Use
---------------

Formal verification can be greatly facilitated by the way the program and its
desired properties are expressed. In the following section, we give some advice
to get as many automatic proofs as possible.

.. _contract cases:

Subprogram Contracts
^^^^^^^^^^^^^^^^^^^^

Preconditions and Postconditions
""""""""""""""""""""""""""""""""

The proof of each subprogram is carried over independently of the
implementation of other subprograms, so the contract of a subprogram should be
strong enough to prove its callers. The contract of a subprogram is usually
expressed as a pair of a precondition and a postcondition:

.. code-block:: ada
   :linenos:

    procedure Incr_Threshold (X : in out Integer) with
      Pre  => X >= 0,
      Post => X = Integer'Min (X'Old + 1, Threshold);

The precondition states the obligation on the caller of the subprogram. For
example, all callers of ``Incr_Threshold`` should ensure that the value passed
in parameter is non-negative before calling ``Incr_Threshold``. The
postcondition states the obligation on the subprogram when it returns. For
example, ``Incr_Threshold`` should always return in a state where the value of
its parameter is the minimum between its value at entry (``X'Old``) incremented
by one, and a given threshold value. This expresses precisely the property of
incrementing until a threshold is reached.

|GNATprove| analyzes the behavior of a subprogram in all possible contexts
allowed by its precondition. It is in this context that it attempts to prove
that the implementation of the subprogram is free of run-time errors and
fulfills its postcondition.

At every call site, |GNATprove| replaces the called subprogram by its
contract. Therefore, it requires that the precondition of the called subprogram
is satisfied, and the only information available when the subprogram returns is
its postcondition.

Note that direct recursive subprograms or mutually recursive subprograms are
treated in this respect exactly like non-recursive ones. Provided the execution
of these subprograms always terminates (a property that is not verified by
|GNATprove|), then it is sound to use their contract at call-site to prove that
their contract hold.

Contract Cases
""""""""""""""

The contract of a subprogram can alternatively be specified as a set of
disjoint and complete contract cases:

.. code-block:: ada
   :linenos:

    procedure Incr_Threshold (X : in out Integer) with
      Contract_Cases => (X < Threshold  => X = X'Old + 1,
                         X >= Threshold => X = X'Old);

Each case in the list consists in a guard and a consequence separated by the
symbol ``=>``. All guards are evaluated on entry to the subprogram. For each
input, only one guard should evaluate to ``True``. The corresponding
consequence should evaluate to ``True`` when returning from the subprogram. For
example, the contract cases of ``Incr_Threshold`` expresses that the subprogram
should be called in two distinct cases only:

* on inputs that are strictly less than the value of a given threshold, in
  which case ``Incr_Threshold`` increments this value.
* on inputs whose value is equal to the given threshold, in which case
  ``Incr_Threshold`` does not modify this value.

Contract cases provide a convenient way to express complex contracts, which
would be cumbersome to express with a precondition and a postcondition. For
example, the contract cases of ``Incr_Threshold`` are equivalent to the
following precondition and postcondition:

.. code-block:: ada
   :linenos:

    procedure Incr_Threshold (X : in out Integer) with
      Pre  => (X < Threshold and not (X = Threshold))
               or else (not (X < Threshold) and X = Threshold),
      Post => (if X'Old < Threshold'Old then X = X'Old + 1
               elsif X'Old = Threshold'Old then X = X'Old);

Note that using contract cases or the equivalent (for run-time checking)
preconditions and postconditions is not equivalent for proof with |GNATprove|.
If contract cases are used, |GNATprove| attempts to prove that they are
disjoint and complete once and for all. If preconditions and postconditions are
used, |GNATprove| treats these properties as any other precondition, so they
must be verified at each call.

Contract cases can also be used in addition to preconditions and
postconditions. In that case, the cases should cover all inputs allowed by the
precondition. For example, the contract of ``Incr_Threshold`` can be written:

.. code-block:: ada
   :linenos:

    procedure Incr_Threshold (X : in out Integer) with
      Pre  => X in 0 .. Threshold,
      Post => X >= X'Old,
      Contract_Cases => (X < Threshold => X = X'Old + 1,
                         X = Threshold => X = X'Old);

Note that the completeness is automatically reached when the last guard is
``others``, denoting all cases not captured by any of the other guard.

Expression Functions
""""""""""""""""""""

Expression functions that do not have a user-defined postcondition are treated
specially by |GNATprove|, which generates an implicit postcondition stating
that their result is equal to the expression that defines them. For example,
the function ``Increment`` defined as an expression function:

.. code-block:: ada

   function Increment (X : Integer) return Integer is (X + 1);

is treated by |GNATprove| as if it had a postcondition:

.. code-block:: ada

   Post => Increment'Result = X + 1;

This postcondition is automatically satisfied, so |GNATprove| does not generate
VCs to check it. Expression functions that have a user-defined postcondition
are treated like regular functions.

Function Calls in Annotations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The contracts of functions called in annotations are essential for automatic
proofs. Currently, the knowledge that a function call in an annotation respects
its postcondition (when called in a context where the precondition is
satisfied) is only available for expression functions. Thus, expression
functions should be used whenever possible for these functions called in
annotations.  The syntax of expression functions, introduced in Ada 2012,
allows defining functions whose implementation simply returns an expression,
such as ``Is_Even``, ``Is_Odd`` and ``Is_Prime`` below.

.. code-block:: ada
   :linenos:

    function Is_Even (X : Integer) return Boolean is (X mod 2 = 0);

    function Is_Odd (X : Integer) return Boolean is (not Even (X));

    function Is_Prime (X : Integer) with
      Pre => Is_Odd (X);

Calls to Standard Library Functions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The standard library for the selected target is pre-analyzed, so that user code
can freely call standard library subprograms.

Loop Invariants
^^^^^^^^^^^^^^^

In order for |GNATprove| to prove formally the properties of interest on
subprograms with loops, the user should annotate these loops with loop
invariants. A loop invariant gives information on the state at entry to the
loop at each iteration. Loop invariants in |SPARK| are expressed with the
``Loop_Invariant`` pragma, which may appear anywhere in the main list of
statements in a loop body, or directly in a chain of nested block statements in
this main list of statements. Only the first ``Loop_Invariant`` pragmas are
used by |GNATprove| as a loop invariant during proof (they should be next to
each other, or separated only by ``Loop_Variant`` pragmas). Other
``Loop_Invariant`` pragmas are proved like regular assertions. Loop invariants
may have to be precise enough to prove the property of interest. For example,
in order to prove the postcondition of function ``Contains`` below, one has to
write a precise loop invariant such as the one given below:

.. code-block:: ada
   :linenos:

   function Contains (Table : IntArray; Value : Integer) return Boolean with
     Post => (if Contains'Result then
                (for some J in Table'Range => Table (J) = Value)
 	     else
                (for all J in Table'Range => Table (J) /= Value));

   function Contains (Table : IntArray; Value : Integer) return Boolean is
   begin
      for Index in Table'Range loop
         pragma Loop_Invariant (for all J in Table'First .. Index - 1 =>
                                 Table (J) /= Value);

         if Table(Index) = Value then
            return True;
         end if;
      end loop;

      return False;
   end Contains;

When the loop involves modifying a variable, it may be necessary to refer to
the value of the variable at loop entry. This can be done using the GNAT
attribute ``'Loop_Entry``. For example, in order to prove the postcondition of
function ``Move`` below, one has to write a loop invariant referring to
``Src'Loop_Entry`` such as the one given below:

.. code-block:: ada
   :linenos:

   procedure Move (Dest, Src : out IntArray) with
     Post => (for all J in Dest'Range => Dest (J) = Src'Old (J));

   procedure Move (Dest, Src : out IntArray) is
   begin
      for Index in Dest'Range loop
         pragma Loop_Invariant ((for all J in Dest'First .. Index - 1 =>
                                  Dest (J) = Src'Loop_Entry (J)) and
                                (for all J in Index .. Dest'Last =>
                                  Src (J) = Src'Loop_Entry (J)));

         Dest (Index) := Src (Index);
         Src (Index) := 0;
      end loop;
   end Move;

Loop Variants
^^^^^^^^^^^^^

Proofs of termination of loops rely on ``Loop_Variant`` pragmas. Proving one
loop variant is sufficient to prove that a loop terminates, even if the loop
contains multiple ``Loop_Variant`` pragmas, and others are not proved. Indeed,
it is sufficient to know that one bounded quantity decreases or increases
monotonically (or a mix of these, as loop invariants may have increasing and
decreasing parts, the order of which fixes the lexicographic combined order of
progress) to be assured that the loop terminates. Note that, in general, this
requires proving also that there are no run-time errors in the loop, to show
that the quantity stays within bounds. Otherwise, the code may still wrap
around at run time (if the code is compiled without checks), and the loop will
not necessarily exit.

The ``Loop_Variant`` pragmas that appear next to the first group of
``Loop_Invariant`` pragmas (or at the start of the loop body if there are no
``Loop_Invariant`` pragmas in the loop) are handled with the most precision by
|GNATprove|, as they become loop variants of the underlying intermediate
representation in Why3. Other ``Loop_Variant`` pragmas are proved by showing
that the quantity that should progress monotonically does so between the
program point where the first group of ``Loop_Invariant`` pragmas appears (or
the start of the loop if there is no such group) and the program point where
the ``Loop_Variant`` pragma appears, and that this quantity either stays the
same or progresses on the rest of the loop.

Quantified Expressions
^^^^^^^^^^^^^^^^^^^^^^

Ada 2012 quantified expressions are a special case with respect to run-time
errors: the enclosed expression must be run-time error free over the *entire
range* of the quantification, not only at points that would actually be
reached at execution. As an example, consider the following expression:

.. code-block:: ada

    (for all I in 1 .. 10 => 1 / (I - 3) > 0)

This quantified expression will never raise a run-time error, because the
test is already false for the first value of the range, ``I = 1``, and the
execution will stop, with the result value ``False``. However, |GNATprove|
requires the expression to be run-time error free over the entire range,
including ``I = 3``, so there will be an unproved VC for this case.

Pragma ``Assert_And_Cut``
^^^^^^^^^^^^^^^^^^^^^^^^^

|GNATprove| may need to consider many possible paths through a subprogram. If
this number of paths is too large, |GNATprove| will take a long time to prove
even trivial properties. To reduce the number of paths analyzed by |GNATprove|,
one may use the pragma ``Assert_And_Cut``, to mark program points where
|GNATprove| can *cut* paths, replacing precise knowledge about execution before
the program point by the assertion given. The effect of this pragma for
compilation is exactly the same as the one of pragma ``Assert``.

For example, in the procedure below, all that is needed to prove that the code
using ``X`` is free from run-time errors is that ``X`` is positive. Without the
pragma, |GNATprove| considers all execution paths through ``P``, which may be
many. With the pragma, |GNATprove| only needs to consider the paths from the
start of the procedure to the pragma, and the paths from the pragma to the end
of the procedure, hence many fewer paths.

.. code-block:: ada
   :linenos:

   procedure P is
      X : Integer;
   begin
      --  complex computation that sets X
      pragma Assert_And_Cut (X > 0);
      --  complex computation that uses X
   end P;

Investigating Failed Proofs
---------------------------

One of the most challenging aspects of formal verification is the analysis of
failed proofs. If |GNATprove| fails to prove automatically that a run-time
check or an assertion holds, there might be various reasons:

* [CODE] The check or assertion does not hold, because the code is wrong.
* [ASSERT] The assertion does not hold, because it is incorrect.
* [SPEC] The check or assertion cannot be proved, because of some missing
  assertions about the behavior of the program.
* [TIMEOUT] The check or assertion is not proved because the prover timeouts.
* [PROVER] The check or assertion is not proved because the prover is not smart
  enough.

Investigating Incorrect Code or Assertion
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

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
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The second step is to consider whether the property is provable [SPEC].  A
check or assertion might be unprovable because a necessary annotation is
missing:

* the precondition of the enclosing subprogram might be too weak; or
* the postcondition of a subprogram called might be too weak; or
* a loop invariant for an enclosing loop might be too weak; or
* a loop invariant for a loop before the check or assertion might be too weak.

In particular, |GNATprove| does not look into subprogram bodies, so all the
necessary information for calls should be explicit in the subprogram
contracts. A focused manual review of the code and assertions can efficiently
diagnose many cases of missing annotations. Even when an assertion is quite
large, |GNATprove| precisely locates the part that it cannot prove, which can
help figuring out the problem. It may useful to simplify the code during this
investigation, for example by adding a simpler assertion and trying to prove
it.

|GNATprove| provides path information that might help the code review. Select
``Prove --> Show Path`` as described in :ref:`GPS integration` to display
inside the editor the path on which the proof failed. In many cases, this is
sufficient to spot a missing assertion. To further assist the user, we plan to
add to this path some information about the values taken by variables from a
counterexample.

.. figure:: static/show_path.jpg
   :align: center
   :alt: GPS displays a path in the source code panel by coloring in blue
         the background of those lines in the path.

   Path displayed in GPS for an unproved property

Investigating Prover Shortcomings
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The last step is to investigate if the prover would find a proof given enough
time [TIMEOUT] or if another prover can find a proof [PROVER]. To that end,
|GNATprove| provides options ``-timeout`` and ``-prover``, usable either from
the command-line (see :ref:`command line`) or inside GPS (see :ref:`GPS
integration`).

Note that for the above experiments, it is quite convenient to use the ``Prove
Line`` or ``Prove Subprogram`` features in GPS, as described in :ref:`GPS
integration`, to get faster results for the desired line or subprogram.

A common limitation of automatic provers is that they don't handle well
non-linear arithmetic. For example, they might fail to prove simple checks
involving multiplication, division, modulo or exponentiation.

In that case, a user may either:

* manually review the unproved checks and record that they can be trusted (for
  example by storing the result of |GNATprove| under version control), or
* add an assumption in the code to help the prover, in the form of a ``pragma
  Assume``. |GNATprove| handles it like an assertion, so it both attempts to
  prove it, and uses it in subsequent code. If the assumption is not proved, it
  can be manually reviewed like mentioned above, and marking it as an assumption
  in the code helps documenting it.

We plan to provide a `user view` of the formula passed to the prover, for
advanced users to inspect. This view will express in an Ada-like syntax the
actual formula whose proof failed, to make it easier for users to interpret it.
This format is yet to be defined.

For very advanced users, in particular those who would like to do manual proof
of VCs, we will provide a description of the format of the VCs generated by
|GNATprove|, so that users can understand the actual VCs passed to the
prover. Each VC is stored in an individual file under the sub-directory
``gnatprove`` of the project object directory (default is the project
directory). The file name follows the convention::

  <file>_<line>_<column>_<check>_<num>.why

where:

* ``file`` is the name of the Ada source file for the check or assertion
* ``line`` is the line where the check or assertion appears
* ``column`` is the column
* ``check`` is an identifier for the check or assertion
* ``num`` is an optional number and identifies different paths through the
  program, between the start of the subprogram and the location of the check or
  assertion

For example, the VCs for a range check at line 160, column 42, of the file
``f.adb`` are stored in::

  f.adb_160_42_range_check.why
  f.adb_160_42_range_check_2.why
  f.adb_160_42_range_check_3.why
  ...

The syntax of these files depend on the prover that was used. By default, it is
Alt-Ergo, so these files are in Why3 proof syntax.

To be able to inspect these files, you should instruct |GNATprove| to keep them
around by adding the switch ``-d`` to |GNATprove|'s command line. You can also
use the switch ``-v`` to get a detailed log of which VCs |GNATprove| is
producing and attempting to prove.

Known Limitations
-----------------

|GNATprove| analyzes floating-point values and operations as if they were over
real numbers, with no rounding. The only rounding that occurs is for static
values (for example ``1.0``) which get rounded to their closest representable
floating-point value, depending on the type used in the code.

In mode ``prove``, the current version has the following limitations:

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
