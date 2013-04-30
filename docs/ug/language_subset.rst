.. _introduction to spark:

***********************
Introduction to |SPARK|
***********************

This chapter provides an overview of the |SPARK| language, detailing for each
feature its consequences in terms of execution and formal verification. This is
not a reference manual for the |SPARK| language, which can be found in:

* the Ada Reference Manual (for Ada features), and
* the |SPARK| Reference Manual (for SPARK-specific features)

More details on how |GNAT Pro| compiles |SPARK| code can be found in the |GNAT
Pro| Reference Manual.

Ada Features That Are Not in |SPARK|
====================================

To facilitate formal verification, |SPARK| enforces a number of global
simplifications to Ada 2012. The most notable simplifications are:

- The use of access types and allocators is not permitted.

- All expressions (including function calls) are free of side-effects.

- Aliasing of names is not permitted.

- The goto statement is not permitted.

- The use of controlled types is not permitted.

- Tasking is not currently permitted.

- Raising and handling of exceptions is not permitted.

Uses of these features in |SPARK| code are detected by |GNATprove| and reported
as errors. Formal verification is not possible on subprograms using these
features.

Combining Code in |SPARK| and Code in Ada
=========================================

Allowed Combinations
--------------------

We describe a program unit or language feature as being "in |SPARK|" if it
complies with the restrictions required to permit formal verification.
Conversely, a program unit language feature is "not in |SPARK|" if it does not
meet these requirements, and so is not amenable to formal verification. Within
a single unit, features which are "in" and "not in" |SPARK| may be mixed at a
fine level. For example, the following combinations may be typical:

- Package specification in |SPARK|. Package body not in |SPARK|.

- Visible part of package specification in |SPARK|. Private part and body not
  in |SPARK|.

- Package specification in |SPARK|. Package body almost entirely in |SPARK|,
  with a small number of subprogram bodies not in |SPARK|.

- Package specification in |SPARK|, with all bodies imported from another
  language.

- Package specification contains a mixture of declarations which are in |SPARK|
  and not in |SPARK|.  The latter declarations are only visible and usable from
  client units which are not in |SPARK|.

Such patterns are intended to allow for application of formal verification to a
subset of a program, and the combination of formal verification with more
traditional testing (see :ref:`proof and test`).

Specifying the Boundary with Pragma ``SPARK_Mode``
--------------------------------------------------

.. todo:: Adapt following to new pragma SPARK_Mode

The user may require that the project only contains code in |SPARK|, by using
option ``--mode=force``. Any violation of |SPARK| is then reported as an error,
and any construct in |SPARK| not yet implemented is reported as a warning.

For a finer-grain control, the user may require that some subprograms are in
|SPARK| by inserting a specific pragma ``Annotate`` in the body of the
subprogram. He may also insert this pragma inside or before a package
declaration (spec or body) to require that all subprogram declarations in this
package are in |SPARK|.

On the following example:

.. code-block:: ada
   :linenos:

    package P is
       pragma Annotate (gnatprove, Force);
       X : access Boolean;
       procedure P0;
    end P;

.. code-block:: ada
   :linenos:

    package body P is
       procedure Set is
       begin
	  X.all := True;
       end Set;

       procedure P0 is
	  Y : Boolean;

	  function Get return Boolean is
	     pragma Annotate (gnatprove, Ignore);
	  begin
	     return X.all;
	  end Get;

	  procedure P1 is
	  begin
	     if not Get then
		return;
	     end if;
	     Y := True;
	  end P1;
       begin
	  Set;
	  P1;
       end P0;
    end P;

|GNATprove| outputs the following errors::

    p.adb:4:07: explicit dereference is not in SPARK
    p.ads:3:08: access type is not in SPARK

The error messages distinguish constructs not in |SPARK| (like a pointer
dereference) from constructs not yet implemented. Notice that no error is given
for the dereference in ``Get``, as another pragma ``Annotate`` in that
subprogram specifies that formal proof should not be done on this subprogram.

|SPARK| Features
================

|SPARK| contains many features for specifying the intended behavior of
programs. Some of these features come from Ada 2012 (preconditions and
postconditions for example). Other features are specific to |SPARK| (loop
ivariants and variants for example). In this section, we describe these
features and their impact on execution and formal verification.

Subprogram Contracts
--------------------

Preconditions and Postconditions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Preconditions and postconditions specify the contract of a subprogram in
Ada 2012. For example:

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

The special attributes ``Result`` and ``Old`` defined in Ada 2012 are allowed
in postconditions only (not in preconditions), to refer respectively to the
result of a function, and the value of an object on subprogram entry.

When compiling with assertions (switch ``-gnata`` in |GNAT Pro|), the resulting
program contains run-time checks that the precondition evaluates to ``True`` on
subprogram entry, and that the postcondition evaluates to ``False`` on
subprogram exit.

.. todo:: Continue from here

A correct contract 

The proof of each subprogram is carried over independently of the
implementation of other subprograms, so the contract of a subprogram should be
strong enough to prove its callers. The contract of a subprogram is usually
expressed as a pair of a precondition and a postcondition:

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

.. _contract cases:

Contract Cases
^^^^^^^^^^^^^^

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
^^^^^^^^^^^^^^^^^^^^

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
---------------

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
-------------

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
----------------------

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
-------------------------

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
