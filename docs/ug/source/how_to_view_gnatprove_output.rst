How to View |GNATprove| Output
==============================

|GNATprove| produces two kinds of outputs: the one which is echoed to standard
output or displayed in your IDE (GPS or GNATbench), and the one which is
produced in a file ``gnatprove.out``, which lies in the ``gnatprove``
subdirectory of the object directory of your project.

.. _The Analysis Results Summary Table:

The Analysis Results Summary Table
----------------------------------

A summary table at the start of file ``gnatprove.out`` provides an overview of
the verification results for all checks in the project. The table may look like
this::

      ----------------------------------------------------------------------------------------------------------------
      SPARK Analysis Results      Total        Flow   Interval                          Provers   Justified   Unproved
      ----------------------------------------------------------------------------------------------------------------
      Data Dependencies               .           .          .                                .           .          .
      Flow Dependencies               .           .          .                                .           .          .
      Initialization               2100        2079          .                                .           .         21
      Non-Aliasing                    .           .          .                                .           .          .
      Run-time Checks               596           .          .    480 (altergo  31%, CVC4  69%)           .        116
      Assertions                      3           .          .      3 (altergo  33%, CVC4  67%)           .          .
      Functional Contracts          323           .          .    168 (altergo  24%, CVC4  76%)           .        155
      LSP Verification                .           .          .                                .           .          .
      ----------------------------------------------------------------------------------------------------------------
      Total                        3022  2079 (69%)          .                        651 (22%)           .   292 (9%)

The following table explains the lines of the summary table:

.. tabularcolumns:: |l|p{5in}|

.. csv-table::
   :header: "Line Description", "Explanation"
   :widths: 1, 5

   "Data Dependencies", "Verification of :ref:`Data Dependencies` and parameter modes"
   "Flow Dependencies", "Verification of :ref:`Flow Dependencies`"
   "Initialization", "Verification of :ref:`Data Initialization Policy`"
   "Non-Aliasing", "Verification of :ref:`Absence of Interferences`"
   "Run-time Checks", "Verification of absence of run-time errors (AoRTE) (except those raising ``Storage_Error``)"
   "Assertions", "Verification of :ref:`Assertion Pragmas`"
   "Functional Contracts", "Verification of functional contracts (includes :ref:`Subprogram Contracts`, :ref:`Package Contracts` and :ref:`Type Contracts`)"
   "LSP Verification", "Verification related to :ref:`Object Oriented Programming and Liskov Substitution Principle`"

We now explain the columns of the table.

* The ``Total`` column describes the total number of checks in this category.

* The ``Flow`` column describes the number of checks proved by flow analysis.

* The ``Interval`` column describes the number of checks (overflow and range
  checks) proved by a simple static analysis of bounds for floating-point
  expressions based on type bounds of sub-expressions.

* The ``Provers`` column describes the number of checks proved by automatic or
  manual provers. The column also gives information on the provers used, and
  the percentage of checks proved by each prover. Note that sometimes a check
  is proved by a combination of provers, hence the use of percentage instead of
  an absolute count. Also note that generally the prover which is run first (as
  determined by the ``--prover`` command line switch) proves the most checks,
  because each prover is called only on those checks that were not previously
  proved. The prover percentages are provided in alphabetical order.

* The ``Justified`` column contains the number of checks for which the user has
  provided a :ref:`Direct Justification with Pragma Annotate`.

* Finally, the column ``Unproved`` counts the checks which have neither been
  proved nor justified.

.. _Categories of Messages:

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

* Information messages are issued to notify the user of limitations of
  |GNATprove| on some constructs, or to prevent possible confusion in
  understanding the output of |GNATprove|. They are also issued to report
  proved checks in some modes of |GNATprove|.

.. _Effect of Mode on Output:

Effect of Mode on Output
------------------------

|GNATprove| can be run in four different modes, as selected with the switch
``--mode=<mode>``, whose possible values are ``check``, ``check_all``,
``flow``, ``prove`` and ``all`` (see :ref:`Running GNATprove from the Command
Line`). The output depends on the selected mode.

In modes ``check`` and ``check_all``, |GNATprove| prints on the standard output
a list of error messages for violations of |SPARK| restrictions on all the code
for which ``SPARK_Mode`` is ``On``.

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

If switch ``--report=all``, ``--report=provers`` or ``--report=statistics`` is
specified, |GNATprove| additionally prints on the standard output information
messages for proved checks.

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
   "predicate check", "Check that the given value respects the applicable type predicate."
   "predicate check on default value", "Check that the default value for the type respects the applicable type predicate."
   "length check", "Check that the given array is of the length of the expected array subtype."
   "discriminant check", "Check that the discriminant of the given discriminated record has the expected value. For variant records, this can happen for a simple access to a record field. But there are other cases where a fixed value of the discriminant is required."
   "tag check",          "Check that the tag of the given tagged object has the expected value."
   "ceiling priority in Interrupt_Priority", "Check that the ceiling priority specified for a protected object containing a procedure with an aspect Attach_Handler is in Interrupt_Priority"
   "interrupt is reserved",   "Check that the interrupt specified by Attach_Handler is not reserved"
   "ceiling priority protocol", "Check that the ceiling priority protocol is respected, i.e., when a task calls a protected operation, the active priority of the task is not higher than the priority of the protected object (ARM Annex D.3)"
   "task termination",   "Check that the task does not terminate, as required by Ravenscar"

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
   "volatile function", E, "A nonvolatile function may not have a volatile global."
   "tasking exclusivity", E, "No two tasks may suspend on the same protected object or the same suspension object."
   "tasking exclusivity", E, "No two tasks may read and write from the same unsynchronized object."
   "missing dependency", "C", "A dependency is missing from the dependency relation."
   "dependency relation", "C", "An out parameter or global is missing from the dependency relation."
   "missing null dependency", "C", "A variable is missing from the null dependency."
   "incorrect dependency", "C", "A stated dependency is not fulfilled."
   "not initialized", "C", "Flow analysis has detected the use of an uninitialized variable."
   "initialization must not depend on something", "C", "Wrong Initializes aspect detected."
   "type is not fully initialized", "C", "A type promised to be default initialized but is not."
   "needs to be a constituent of some state abstraction", "C", "Flow analysis detected a constituent that has to be exposed through some state abstraction."
   "constant after elaboration", "C", "An object which is constant after elaboration must not be changed after elaboration and as such cannot be the output of any subprogram."
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
   "volatile function", E, "A volatile function that has no volatile globals does not have to be a volatile function."

.. note::

   Certain messages emitted by flow analysis are classified as errors
   and consequently cannot be suppressed or justified.

.. _Understanding Counterexamples:

Understanding Counterexamples
-----------------------------

When a check cannot be proved, |GNATprove| may generate a counterexample. A
counterexample consists in two parts:

* a path (or set of paths) through the subprogram
* an assignment of values to variables that appear on that path

The best way to look at a counterexample is to display it in GPS by clicking on
the icon to the left of the failed proof message, or to the left of the
corresponding line in the editor (see :ref:`Running GNATprove from
GPS`). |GNATprove| then displays the path in one color, and the values of
variables on the path by inserting lines in the editor only (not in the file)
which display these values. For example, consider procedure ``Counterex``:

.. literalinclude:: ../gnatprove_by_example/examples/counterex.adb
   :language: ada
   :linenos:

The assertion on line 11 may fail when input parameter ``Cond`` is ``True`` and
input parameters ``I1`` and ``I2`` are too big. The counterexample generated by
|GNATprove| is displayed as follows in GPS, where each line highlighted in the
path is followed by a line showing the value of variables from the previous
line:

.. image:: ../static/counterexample.png
   :width: 800 px
   :alt: Counterexample in GPS

|GNATprove| also completes the message for the failed proof with an explanation
giving the values of variables from the checked expression for the
counterexample. Here, the message issued by |GNATprove| on line 11 gives the
value of output parameter ``R``:

.. literalinclude:: ../gnatprove_by_example/results/counterex.prove
   :language: none
   :lines: 7

The counterexample generated by |GNATprove| does not always correspond to a
feasible execution of the program:

#. When some contracts or loop invariants are missing, thus causing the
   property to become unprovable (see details in section on :ref:`Investigating
   Unprovable Properties`), the counterexample may help point to the missing
   contract or loop invariant. For example, the postcondition of procedure
   ``Double_In_Call`` is not provable because the postcondition of the function
   ``Double`` that it calls is too weak, and the postcondition of procedure
   ``Double_In_Loop`` is not provable because its loop does not have a loop
   invariant:

   .. literalinclude:: ../gnatprove_by_example/examples/counterex_unprovable.ads
      :language: ada
      :linenos:

   .. literalinclude:: ../gnatprove_by_example/examples/counterex_unprovable.adb
      :language: ada
      :linenos:

   The counterexample generated by |GNATprove| in both cases shows that the
   prover could deduce wrongly that ``X`` on ouput is -3 when its value is 1 on
   input, due to a missing contract in the function called or a missing loop
   invariant the loop executed:

   .. literalinclude:: ../gnatprove_by_example/results/counterex_unprovable.prove
      :language: none

#. When some property cannot be proved due to prover shortcomings (see details
   in section on :ref:`Investigating Prover Shortcomings`), the counterexample
   may explain why the prover cannot prove the property. However, note that
   since the counterexample is always generated only using CVC4 prover, it can
   just explain why this prover cannot prove the property. Also note that if
   CVC4 is not selected and generating of a counterexample is not disabled by
   ``--no-counterexample`` switch, a counterexample is still attempted to be
   generated using CVC4, but the proof result of CVC4 is not taken into account
   in this case.

#. When using a short value of timeout or steps, the prover may hit the
   resource bound before it has produced a full counterexample. In such a case,
   the counterexample produced may not correspond to a feasible execution.

#. When the value of ``--proof`` switch is ``per_check`` (the default value),
   then the counterexample gives values to variables on all paths through the
   subprogram, not only the path which corresponds to the feasible
   execution. One can rerun |GNATprove| with value ``progressive`` or
   ``per_path`` to separate possible execution paths in the counterexample.
