.. _SPARK Tutorial:

****************
|SPARK| Tutorial
****************

This chapter describes a simple use of the |SPARK| toolset on a program written
completely in |SPARK|, within the GPS integrated development environment. All
the tools may also be run from the command-line, see :ref:`Command Line
Invocation`.

.. note::

  If you're using SPARK Discovery instead of SPARK Pro, some of the proofs in
  this tutorial may not be obtained automatically. See the section on
  :ref:`Alternative_Provers` to install additional provers that are not present
  in SPARK Discovery.

Writing |SPARK| Programs
========================

As a running example, we consider a naive searching algorithm for an unordered
collection of elements. The algorithm returns whether the collection contains
the desired value, and if so, at which index. The collection is implemented
here as an array. We deliberately start with an incorrect program for package
``Search``, in order to explain how the |SPARK| toolset can help correct these
errors. The final version of the ``linear_search`` example is part of the
:ref:`Examples in the Toolset Distribution`.

We start with creating a GNAT project file in ``search.gpr``:

.. literalinclude:: /examples/linear_search_ada/search.gpr
   :language: ada
   :linenos:

It specifies that the source code to inspect is in the current directory, and
that the code should be compiled at maximum warning level (switch
``-gnatwa``). GNAT projects are used by most tools in the |GNAT Pro| toolsuite;
for in-depth documentation of this technology, consult the |GNAT Pro|
User's Guide. Documentation and examples for the |SPARK| language and tools are
also available via the :menuselection:`Help --> SPARK` menu in GPS.

The obvious specification of ``Linear_Search`` is given
in file ``linear_search.ads``, where
we specify that the spec is in |SPARK| by using aspect ``SPARK_Mode``.

.. literalinclude:: /examples/linear_search_ada/linear_search.ads
   :language: ada
   :linenos:

The implementation of ``Linear_Search`` is given in
file ``linear_search.adb``, where we specify
that the body is in |SPARK| by using aspect ``SPARK_Mode``.  It is as obvious
as its specification, using a loop to go through the array parameter ``A`` and
looking for the first index at which ``Val`` is found, if there is such an
index.

.. literalinclude:: /examples/linear_search_ada/linear_search.adb
   :language: ada
   :linenos:

We can check that the above code is valid Ada by using the ``Build > Check
Semantic`` menu, which completes without any errors or warnings:

.. image:: /static/search_check_semantic.png

Checking SPARK Legality Rules
-----------------------------

Now, let us run |GNATprove| on this unit, using the :menuselection:`SPARK -->
Examine File` menu, so that it issues errors on |SPARK| code that violates
|SPARK| rules:

.. image:: /static/search_examine.png

It detects here that function ``Search`` is not in |SPARK|, because it has
an ``out`` parameter:

.. image:: /static/search_not_spark.png

The permission in Ada 2012 to have ``out`` parameters to functions is not
allowed in |SPARK|, because it causes calls to have side-effects (assigning to
their ``out`` parameters), which means that various calls in the same
expression may be conflicting, yielding different results depending on the
order of evaluation of the expression.

We correct this problem by defining a record type ``Search_Result`` in
``linear_search.ads`` holding both the Boolean result and the index for cases
when the value is found, and making ``Search`` return this type:

.. literalinclude:: /examples/linear_search_spark/linear_search.ads
   :language: ada
   :linenos:

The implementation of ``Search`` in ``linear_search.adb`` is modified to use
this type:

.. literalinclude:: /examples/linear_search_spark/linear_search.adb
   :language: ada
   :linenos:

.. _Checking SPARK Initialization Policy:

Checking SPARK Initialization Policy
------------------------------------

Re-running |GNATprove| on this unit, still using the :menuselection:`SPARK -->
Examine File` menu, now reports a different kind of error. This time it is the
static analysis pass of |GNATprove| called *flow analysis* that detects an
attempt of the program to return variable ``Res`` while it is not fully
initialized, thus violating the initialization policy of |SPARK|:

.. image:: /static/search_flow_error.png

Inside the GPS editor, we can click on the icon, either on the left of the
message, or on line 23 in file ``linear_search.adb``, to show the path on which
``Res.At_Index`` is not initialized:

.. image:: /static/search_flow_error_path.png

Another click on the icon makes the path disappear.

This shows that, when the value is not found, the component ``At_Index`` of the
value returned is indeed not initialized. Although that is allowed in Ada,
|SPARK| requires that all inputs and outputs of subprograms are completely
initialized (and the value returned by a function is such an output). As a
solution, we could give a dummy value to component ``At_Index`` when the search
fails, but we choose here to turn the type ``Search_Result`` in
``linear_search.ads`` into a discriminant record, so that the component
``At_Index`` is only usable when the search succeeds:

.. literalinclude:: /examples/linear_search_prove/linear_search.ads
   :language: ada
   :linenos:
   :lines: 10-17

Then, in the implementation of ``Search`` in ``linear_search.adb``, we change
the value of the discriminant depending on the success of the search:

.. literalinclude:: /examples/linear_search_prove/linear_search.adb
   :language: ada
   :linenos:
   :lines: 5-24

Now re-running |GNATprove| on this unit, using the :menuselection:`SPARK -->
Examine File` menu, shows that there are no reads of uninitialized data.

Writing Functional Contracts
----------------------------

We now have a valid SPARK program. It is not yet very interesting |SPARK| code
though, as it does not contain any contracts, which are necessary to be able to
apply formal verification modularly on each subprogram, independently of the
implementation of other subprograms. The precondition constrains the value of
input parameters, while the postcondition states desired properties of the
result of the function. See :ref:`Preconditions` and :ref:`Postconditions` for
more details. Here, we can require in the precondition of ``Search`` in
``linear_search.ads`` that callers of ``Search`` always pass a non-negative
value for parameter ``Val``, and we can state that, when the search succeeds,
the index returned points to the desired value in the array:

.. literalinclude:: /examples/linear_search_contract/linear_search.ads
   :language: ada
   :linenos:
   :lines: 21-27

Notice the use of an if-expression in the postcondition to express an
implication: if the search succeeds it implies that the value at the returned index
is the value that was being searched for. Note also the use of ``Search'Result``
to denote the value returned by the function.

This contract is still not very strong. Many faulty implementations of the
search would pass this contract, for example one that always fails (thus
returning with ``Search'Result.Found = False``). We could reinforce the
postcondition, but we choose here to do it through a contract by cases, which
adds further constraints to the usual contract by precondition and
postcondition. We want to consider here three cases:

* the desired value is found at the first index (1)
* the desired value is found at other indexes (2 to 10)
* the desired value is not found in the range 1 to 10

In the first case, we want to state that the index returned is 1. In the second
case, we want to state that the search succeeds. In the third case, we want to
state that the search fails. We use a helper function ``Value_Found_In_Range``
in ``linear_search.ads`` to express that a value ``Val`` is found in an array
``A`` within given bounds ``Low`` and ``Up``:

.. literalinclude:: /examples/linear_search_contract/linear_search.ads
   :language: ada
   :linenos:
   :lines: 15-34

Note that we express ``Value_Found_In_Range`` as an expression function, a
function whose body consists of a single expression, which can be given in a
specification file.

Note also the use of quantified expressions to express properties over
collections: ``for some`` in ``Value_Found_In_Range`` expresses an existential
property (there exists an index in this range such that ...), ``for all`` in
the third contract case expresses a universal property (all indexes in this
range are such that ...).

Each contract case consists of a guard (on the left of the arrow symbol)
evaluated on subprogram entry, and a consequence (on the right of the arrow
symbol) evaluated on subprogram exit. The special expression
``Search'Result`` may be used in consequence expressions. The three
guards here should cover all possible cases, and be disjoint. When a contract
case is activated (meaning its guard holds on entry), its consequence should
hold on exit.

The program obtained so far is a valid |SPARK| program, which |GNAT Pro|
analyzes semantically without errors or warnings.

Testing |SPARK| Programs
========================

We can compile the above program, and test it on a set of selected inputs. The
following test program in file ``test_search.adb`` exercises the case where the
searched value is present in the array and the case where it is not:

.. literalinclude:: /examples/linear_search_contract/test_search.adb
   :language: ada
   :linenos:

We can check that the implementation of ``Linear_Search`` passes this test by
compiling and running the test program:

.. code-block:: bash

   $ gnatmake test_search.adb
   $ test_search
   > OK: Found existing value at first index
   > OK: Did not find non-existing value

.. note::

   We use above the command-line interface to compile and run the test program
   ``test_search.adb``. You can do the same inside GPS by selecting the menu
   :menuselection:`Project --> Properties` and inside the panel
   :guilabel:`Main` of folder :guilabel:`Sources`, add ``test_search.adb`` as a
   main file. Then, click :guilabel:`OK`. To generate the ``test_search``
   executable, you can now select the menu :menuselection:`Build --> Project
   --> test_search.adb` and to run the ``test_search`` executable, you can
   select the menu :menuselection:`Build --> Run --> test_search`.

But only part of the program was really tested, as the contract was not checked
during execution. To check the contract at run time, we recompile with the
switch ``-gnata`` (``a`` for assertions, plus switch ``-f`` to force
recompilation of sources that have not changed):

* a check is inserted that the precondition holds on subprogram entry
* a check is inserted that the postcondition holds on subprogram exit
* a check is inserted that the guards of contract cases are disjoint on
  subprogram entry (no two cases are activated at the same time)
* a check is inserted that the guards of contract cases are complete on
  subprogram entry (one case must be activated)
* a check is inserted that the consequence of the activated contract case holds
  on subprogram exit

Note that the evaluation of the above assertions may also trigger other
run-time check failures, like an index out of bounds. With these additional
run-time checks, an error is reported when running the test program:

.. code-block:: bash

   $ gnatmake -gnata -f test_search.adb
   $ test_search
   > raised SYSTEM.ASSERTIONS.ASSERT_FAILURE : contract cases overlap for subprogram search

.. note::

   We use above the command-line interface to add compilation switch ``-gnata``
   and force recompilation with switch ``-f``. You can do the same inside GPS
   by selecting the menu :menuselection:`Project --> Properties` and inside the
   panel :guilabel:`Ada` of the subfolder :guilabel:`Switches` of folder
   :guilabel:`Build`, select the checkbox :guilabel:`Enable assertions`. Then,
   click :guilabel:`OK`. To force recompilation with the new switch, you can
   now select the menu :menuselection:`Build --> Clean --> Clean All` followed
   by recompilation with :menuselection:`Build --> Project -->
   test_search.adb`. Then run the ``test_search`` executable with
   :menuselection:`Build --> Run --> test_search`.

It appears that two contract cases for ``Search`` are activated at the same
time! More information can be generated at run time if the code is compiler
with the switch ``-gnateE``:

.. code-block:: bash

   $ gnatmake -gnata -gnateE -f test_search.adb
   $ test_search
   > raised SYSTEM.ASSERTIONS.ASSERT_FAILURE : contract cases overlap for subprogram search
   >   case guard at linear_search.ads:33 evaluates to True
   >   case guard at linear_search.ads:35 evaluates to True

It shows here that the guards of the first and second contract cases hold at
the same time. This failure in annotations can be debugged with ``gdb`` like a
failure in the code (provided the program was compiled with appropriate
switches, like ``-g -O0``). The stack trace inside GPS shows that the error
occurs on the first call to ``Search`` in the test program:

.. image:: /static/search_gdb.png

Indeed, the value 1 is present twice in the array, at indexes 1 and 8, which
makes the two guards ``A(1) = Val`` and ``Value_Found_In_Range (A, Val, 2,
10)`` evaluate to ``True``. We correct the contract of ``Search`` in
``linear_search.ads`` by strengthening the guard of the second contract case,
so that it only applies when the value is not found at index 1:

.. literalinclude:: /examples/linear_search_flow/linear_search.ads
   :language: ada
   :linenos:
   :lines: 28-34

With this updated contract, the test passes again, but this time with
assertions checked at run time:

.. code-block:: bash

   $ gnatmake -gnata test_search.adb
   $ test_search
   > OK: Found existing value at first index
   > OK: Did not find non-existing value

The program obtained so far passes successfully a test campaign (of one test!)
that achieves 100% coverage for all the common coverage criteria, once
impossible paths have been ruled out: statement coverage, condition coverage,
the MC/DC coverage used in avionics, and even the full static path coverage.

.. _proving spark programs:

Proving |SPARK| Programs
========================

Formal verification of |SPARK| programs is a two-step process:

1. the first step checks that flows through the program correctly implement the
   specified flows (if any), and that all values read are initialized.
2. the second step checks that the program correctly implement its specified
   contracts (if any), and that no run-time error can be raised.

Step 1 is implemented as a static analysis pass in the tool |GNATprove|, in
``flow`` mode. We have seen this flow analysis at work earlier (see
:ref:`Checking SPARK Initialization Policy`). Step 2 is implemented as a
deductive verification (a.k.a. `proof`) pass in the tool |GNATprove|, in the
default ``all`` mode.

The difference between these two steps should be emphasized. Flow analysis in
step 1 is a terminating algorithm, which typically takes 2 to 10 times as long
as compilation to complete. Proof in step 2 is based on the generation of
logical formulas for each check to prove, which are then passed on to automatic
provers to decide whether the logical formula holds or not. The generation of
logical formulas is a translation phase, which typically takes 10 times as long
as compilation to complete. The automatic proof of logical formulas may take a
very long time, or never terminate, hence the use of a timeout (1s at proof
level 0) for each call to the automatic provers. It is this last step which
takes the most time when calling |GNATprove| on a program, but it is also a
step which can be completely parallelized (using switch ``-j`` to specify the
number of parallel processes): each logical formula can be proved
independently, so the more cores are available the faster it completes.

.. note::

   The proof results presented in this tutorial may slightly vary from
   the results you obtain on your machine, as automatic provers may take
   more or less time to complete a proof depending on the platform and machine
   used.

Let us continue with our running example. This time we will see how step 2
works to prove contracts and absence of run-time errors, using the main
mode ``all`` of |GNATprove| reached through the :menuselection:`SPARK -->
Prove File` menu.

.. image:: /static/search_prove_file.png

.. note::

   The proof panels presented in this tutorial correspond to an advanced user
   profile. A simpler proof panel is displayed when the basic user profile is
   selected (the default). You can switch to the advanced user profile in menu
   :menuselection:`Edit --> Preferences --> SPARK`, by changing the value of
   :guilabel:`User profile` from ``Basic`` to ``Advanced``. See :ref:`Running
   GNATprove from GPS` for details.

We use the default settings and click on :menuselection:`Execute`. It completes
in a few seconds, with a message stating that some checks could not be proved:

.. image:: /static/search_not_proved.png

Note that there is no such message on the postcondition of ``Search``,
which means that it was proved. Likewise, there are no such messages on the
body of ``Search``, which means that no run-time errors can be raised
when executing the function.

These messages correspond to checks done when exiting from ``Search``. It is
expected that not much can be proved at this point, given that the body of
``Search`` has a loop but no loop invariant, so the formulas generated for
these checks assume the worst about locations modified in the loop. A loop
invariant is a special pragma ``Loop_Invariant`` stating an assertion in a
loop, which can be both executed at run-time like a regular pragma ``Assert``,
and used by |GNATprove| to summarize the effect of successive iterations of the
loop. We need to add a loop invariant in ``linear_search.adb`` stating enough
properties about the cumulative effect of loop iterations, so that the contract
cases of ``Search`` become provable. Here, it should state that the value
searched was not previously found:

.. literalinclude:: /examples/linear_search_loopinv/linear_search.adb
   :language: ada
   :lines: 19-20

As stated above, this invariant holds exactly between the two statements in the
loop in ``linear_search.adb`` (after the if-statement, before the increment of
the index). Thus, it should be inserted at this place. With this loop
invariant, two checks previously not proved are now proved, and a check
previously proved becomes unproved:

.. image:: /static/search_loopinv.png

The new unproved checks may seem odd, since all we did was add information in
the form of a loop invariant. The reason is that we also removed information at
the same time. By adding a loop invariant, we require |GNATprove| to prove
iterations around the (virtual) loop formed by the following steps:

#. Take any context satisfying the loop invariant, which summarizes all
   previous iterations of the loop.
#. Execute the end of a source loop iteration (just the increment here).
#. Test whether the loop exits, and continue with values which do not exit.
#. Execute the start of a source loop iteration (just the if-statement here).
#. Check that the loop invariant still holds.

Around this virtual loop, nothing guarantees that the index ``Pos`` is
below the maximal index at step 2 (the increment), so the range check
cannot be proved. It was previously proved because, in the absence of a
loop invariant, |GNATprove| proves iterations around the source loop, and
then we get the information that, since the loop did not exit, its test
``Pos < A'Last`` is false, so the range check can be proved.

We solve this issue by setting the type of ``Pos`` in ``linear_search.adb`` to
the base type of ``Index``, which ranges past the last value of
``Index``. (This may not be the simplest solution, but we use it here for the
dynamics of this tutorial.)

.. literalinclude:: /examples/linear_search_loopinv_ok/linear_search.adb
   :language: ada
   :lines: 9

And we add the range information for ``Pos`` to the loop invariant in
``linear_search.adb``:

.. literalinclude:: /examples/linear_search_loopinv_ok/linear_search.adb
   :language: ada
   :lines: 19-22

This allows |GNATprove| to prove the range check, but not the contract:

.. image:: /static/search_contract_not_proved.png

This is actually progress! Indeed, the loop invariant should be strong enough
to:

#. prove the absence of run-time errors in the loop and after the loop
#. prove that it is preserved from iteration to iteration
#. prove the postcondition and contract cases of the subprogram

So we have just achieved goal 1 above!

As we have modified the code and annotations, it is a good time to compile and
run our test program, before doing any more formal verification work. This
helps catch bugs early, and it's easy to do! In particular, the loop
invariant will be dynamically checked at each iteration through the loop.
Here, testing does not show any problems:

.. code-block:: bash

   $ gnatmake -gnata test_search.adb
   $ test_search
   > OK: Found existing value at first index
   > OK: Did not find non-existing value

The next easy thing to do is to increase the timeout of automatic provers. Its
default of 1s is deliberately low, to facilitate interaction with |GNATprove|
during the development of annotations, but it is not sufficient to prove the
more complex checks. Let's increase it to 10s (or equivalently set the ``Proof
level`` to 2 in the proof panel corresponding to a basic user profile), and
rerun |GNATprove|:

.. image:: /static/search_10s_timeout.png

The unproved check remains in the contract cases of ``Linear_Search``. The next
step is to use the :menuselection:`SPARK --> Prove Line` contextual menu
available on line 35:

.. image:: /static/search_prove_line.png

We select the ``Progressively split`` value for choice ``Proof strategy`` in
the window raised in order to maximize proof precision (or equivalently set the
``Proof level`` to 3 in the proof panel corresponding to a basic user profile),
and click on :menuselection:`Execute`:

.. image:: /static/search_prove_line_by_path.png

This runs |GNATprove| only on the checks that originate from line 35, in a
special mode which considers separately individual execution paths if
needed. The check is still not proved, but GPS now displays an icon, either on
the left of the message, or on line 35 in file ``linear_search.ads``, to show the path
on which the contract case is not proved:

.. image:: /static/search_path_info.png

This corresponds to a case where the implementation of ``Search`` does not find
the searched value, but the guard of the second contract case holds, meaning
that the value is present in the range 2 to 10. Looking more closely at the
path highlighted, we can see that the loop exits when ``Pos = A'Last``, so the
value 10 is never considered! We correct this bug by changing the loop test in
``linear_search.adb`` from a strict to a non-strict comparison operation:

.. literalinclude:: /examples/linear_search_no_variant/linear_search.adb
   :language: ada
   :lines: 12

On this modified code, we rerun |GNATprove| on line 35, checking the box
``Report checks proved`` to get information even when a check is proved. The
reassuring green color (and the accompanying info message) show that the check
was proved this time:

.. image:: /static/search_case_proved.png

As usual after code changes, we rerun the test program, which shows no
errors. Rerunning |GNATprove| on the complete file shows no more unproved
checks. The ``Linear_Search`` unit has been fully proved. To see all the checks that
were proved, we can rerun the tool with box ``Report checks proved`` checked,
which displays the results previously computed:

.. image:: /static/search_all_proved.png

Note that one thing that was not proved is that ``Search``
terminates. As it contains a while-loop, it could loop forever. To prove that
it is not the case, we add a loop variant, which specifies a quantity varying
monotonically with each iteration. Since this quantity is bounded by its type,
and we have proved absence of run-time errors in ``Search``, proving
this monotonicity property also shows that there cannot be an infinite number
of iterations of the loop. The natural loop variant for ``Search`` is
the index ``Pos``, which increases at each loop iteration:

.. literalinclude:: /examples/linear_search_final_cases/linear_search.adb
   :language: ada
   :lines: 23

With this line inserted after the loop invariant in ``linear_search.adb``, the
test program still runs without errors (it checks dynamically that the loop
variant is respected), and the program is still fully proved. Here is the final
version of ``Linear_Search``, with the complete annotations:

.. literalinclude:: /examples/linear_search_final_cases/linear_search.ads
   :language: ada
   :linenos:

.. literalinclude:: /examples/linear_search_final_cases/linear_search.adb
   :language: ada
   :linenos:

The final version of the ``linear_search`` example is part of the
:ref:`Examples in the Toolset Distribution`. This concludes our tutorial on the
|SPARK| toolset.
