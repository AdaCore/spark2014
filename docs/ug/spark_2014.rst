.. _introduction to SPARK:

****************************
Overview of |SPARK| Language
****************************

This chapter provides an overview of the |SPARK| language, detailing for each
feature its consequences in terms of execution and formal verification. This is
not a reference manual for the |SPARK| language, which can be found in:

* the Ada Reference Manual (for Ada features), and
* the |SPARK| Reference Manual (for SPARK-specific features)

More details on how |GNAT Pro| compiles |SPARK| code can be found in the |GNAT
Pro| Reference Manual.

The |SPARK| Subset of Ada
=========================

To facilitate formal verification, |SPARK| enforces a number of global
simplifications to Ada 2012. The most notable simplifications are:

- The use of access types and allocators is not permitted.

- All expressions (including function calls) are free of side-effects.

- Aliasing of names is not permitted.

- The goto statement is not permitted.

- The use of controlled types is not permitted.

- Raising and handling of exceptions is not currently permitted (exceptions can
  be included in a program but proof must be used to show that they cannot be
  raised).

Uses of these features in |SPARK| code are detected by |GNATprove| and reported
as errors. Formal verification is not possible on subprograms using these
features.

The features listed above are excluded from |SPARK| because, currently, they defy
formal verification. As formal verification technology advances the list will be
revisited and it may be possible to relax some of these restrictions. There are
other features which are technically feasible to formally verify but which were
excluded from Release 1 of the |SPARK| language and tools for scheduling reasons.
These are scheduled for inclusion in Release 2, the most notable items being
support for tasking and tagged types.

Identifying |SPARK| Code
========================

In general a program can have some parts that are in |SPARK| (and follow all
the rules in the |SPARK| Reference Manual), and some parts that are full
Ada 2012. Pragma or aspect ``SPARK_Mode`` is used to identify which parts are
in |SPARK| (by default programs are in full Ada).

This section contains a simple description of pragma and aspect
``SPARK_Mode``. See :ref:`Pragma_SPARK_Mode` for the complete description.

Note that |GNATprove| only analyzes parts of the code that are identified as
being in |SPARK| using pragma or aspect ``SPARK_Mode``.

Placement Rules
---------------

The form of a pragma SPARK_Mode is as follows:

.. code-block:: ada

   pragma SPARK_Mode [ (On | Off) ]

For example:

.. code-block:: ada

   pragma SPARK_Mode (On);
   package P is

The form of an aspect SPARK_Mode is as follows:

.. code-block:: ada

   [ On | Off ]

For example:

.. code-block:: ada

   package P
      with SPARK_Mode => On
   is

A default argument of On is assumed for any SPARK_Mode pragma or
aspect for which no argument is explicitly specified.

For example:

.. code-block:: ada

   package P is
      pragma SPARK_Mode;  --  On is implicit here

or

.. code-block:: ada

   package P
      with SPARK_Mode  --  On is implicit here
   is

The SPARK_Mode pragma can be used in the following places:

* As a configuration pragma, in which case it sets the default mode for
  all units compiled with this pragma.

* Immediately following a library-level subprogram spec

* Immediately within a library-level package body

* Immediately following the ``private`` keyword of a library-level package spec

* Immediately following the ``begin`` keyword of a library-level package body

* Immediately within a library-level subprogram body

Normally a subprogram or package spec/body inherits the current mode
that is active at the point it is declared. But this can be overridden
by pragma within the spec or body as above.

Consistency Rules
-----------------

The basic rule is that you can't turn SPARK_Mode back On, once you
have explicitly (with a pragma) turned if Off. So the following rules
apply:

If a subprogram spec has SPARK_Mode Off, then the body cannot have
SPARK_Mode On.

For a package, we have four parts:

#. the package public declarations
#. the package private part
#. the body of the package
#. the elaboration code after ``begin``

For a package, the rule is that if you explicitly turn SPARK_Mode
Off for any part, then all the following parts cannot have SPARK_Mode
On. Note that this may require repeating a pragma SPARK_Mode (Off)
in the body. For example, if we have a configuration pragma
SPARK_Mode (On) that turns the mode on by default everywhere, and
one particular package spec has pragma SPARK_Mode (Off), then that
pragma will need to be repeated in the package body.

|SPARK| Features
================

|SPARK| contains many features for specifying the intended behavior of
programs. Some of these features come from Ada 2012 (preconditions and
postconditions for example). Other features are specific to |SPARK| (globals,
and loop invariants for example). In this section, we describe these
features and their impact on execution and formal verification.

Subprogram Contracts
--------------------

|SPARK| provides features to strengthen the contracts on Ada subprograms to
enable more in-depth verification to be performed. The more information is
provided in a contract, the more verification can be performed by the |SPARK|
tools to check that the contracts are satisfied. This ranges from data-flow and
information-flow analysis through to formal proof of robustness and
correctness properties.

.. _Globals:

Globals
^^^^^^^

The data-flow analysis performed by the |SPARK| tools considers the initialization
of variables and the data dependencies of subprograms (which variables are read
or written). This type of analysis can detect errors such as attempting to read
from a variable which has not been assigned a value. In order to perform data-flow
analysis, the tools need to know the complete set of variables which may be read
or written by each subprogram, which consists of any formal parameters of the
subprogram and any global variables used by the subprogram. This set of global
variables may be specified by the programmer via the global annotation, as in
this example:

.. code-block:: ada
   :linenos:

   procedure Add_To_Total (X : in Integer)
      with Global => (In_Out => Total);

This states that the global variable ``Total`` is both an input and an output of the
subprogram (it is both read and written). If such a Global annotation is
present then it will be used in the analysis of calls to the subprogram - callers
may assume that ``Total`` is both read and written and, very importantly, that no
other global variables are read or written by this subprogram. Then, when the body
of the subprogram is analyzed, the tools will check that its implementation satisfies
this contract.

If the Global annotation is not explicitly provided then the tools can derive it
automatically from the body of the subprogram. This may be appropriate in a number
of situations, for example:

- Code has been developed as |SPARK| but not all the aspects are included on all
  subprograms by the developer. This is regarded as *generative analysis*, where
  the code was written with the intention that it would be analyzed.

- Code is in maintenance phase, it might or might not have all of the |SPARK|
  Global aspects. If the Global aspects are present, the synthesized aspects
  may be compared with the explicit ones to update the aspects if the changes
  are acceptable. If there are aspects missing, they are automatically
  synthesized for analysis purposes. This is also regarded as generative
  analysis.

- Legacy code is analyzed which has no (or incomplete) |SPARK| specific aspects
  This is regarded as *retrospective analysis*, where code is being analyzed
  that was not originally written with analysis in mind.

.. _Abstract_State and Initializes:

Abstract_State, Refined_State and Initializes
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The previous section discussed the Global annotation, which applies to subprograms.
There are two more annotations required for data-flow analysis, and these apply to
packages rather than subprograms. Consider the specification of ``Add_To_Total``
above. The global variable ``Total`` might well be declared in the body of the enclosing
package. If the specification of ``Add_To_Total`` appears in the package specification,
then its global annotation is referring to a variable ``Total`` about which nothing
is known because the package body has not yet been analyzed. Indeed, the package
body might not even have been written yet. The Abstract_State annotation allows
us to announce the presence of variables declared within packages.

.. code-block:: ada
   :linenos:

   package P
      with Abstract_State => Total
   is
      procedure Add_To_Total (X : in Integer)
         with Global => (In_Out => Total);
   end P;

Any state (typically a variable or collection of variables) declared within a
package specification or body (but not within a subprogram of the package) must
be announced in the package's Abstract_State annotation. As with the global
annotation described above, the Abstract_State annotation may be stated
explicitly by the programmer or it may be derived automatically by the tools
depending on the circumstances.

The language also provides facilities for combining multiple items of package state
(which could be variables of the package itself, or state from its child packages
or embedded packages) into a single item of Abstract_State (hence the name). There
are also facilities for dealing with volatile state representing inputs or outputs
at the interface with the environment. However these are outside the scope of this
overview.

In the example given above, when performing the flow analysis of any call to
``Add_To_Total`` the tools will check that ``Total`` has previously been assigned a
value. This is necessary because the global annotation states that ``Add_To_Total``
reads the value of ``Total``, so if ``Total`` is undefined then a flow error will result.
In order to perform this flow analysis for the whole program the tools need to
know which elements of package state are initialized when the main program
starts executing and which are still uninitialized. This is the purpose of the
initializes annotation - it tells us what is initialized by the elaboration of
the package. In our example, package ``P`` does initialize ``Total`` so this is specified
by the initializes annotation.

.. code-block:: ada
   :linenos:

   package P
      with Abstract_State => Total,
           Initializes    => Total
   is
      procedure Add_To_Total (X : in Integer)
         with Global => (In_Out => Total);
   end P;

   package body P
      with Refined_State => (Total => T)
   is
      T : Integer := 0;

If state is initialized by the package then it must appear in an initializes
annotation. If it is not initialized then it must not appear in the annotation.
Once again, the initializes annotation may be derived automatically by the tools
if not provided explicitly by the programmer.

Note also the use of the Refined_State annotation in the package body. Each item
named in the Abstract_State annotation in the package specification may be refined
onto many constituents in the package body. This is done by means of the Refined_State
annotation. In this case there is a one-to-one mapping between the abstract view in
the specification (``Total``) and the refined view in the body (``T``) but it could
be a one-to-many relationship or even, in special cases, a one-to-null relationship.

.. _Depends:

Depends
^^^^^^^

The Depends annotation adds more detail to subprogram contracts by specifying
the relationship between the inputs and the outputs.

.. code-block:: ada
   :linenos:

   procedure Swap (X, Y : in out Integer)
      with Depends => (X => Y,
                       Y => X);

In the example above the Depends annotation states that the final value of ``X``
depends on the initial value of ``Y``, and the final value of ``Y`` depends on the
initial value of ``X``. It is important to note that this is not stating the
stronger property that the values of ``X`` and ``Y`` are swapped - that would require
a postcondition aspect which will be described in the next section. So an
implementation which, for example, doubled ``X`` and ``Y`` and then swapped their
values would satisfy this dependency. If a Depends annotation is present then
it must be complete: for every output of the subprogram it must specify
the (possibly null) list of inputs on which that output depends.

The Depends aspect of a subprogram is used by the tools when performing flow
analysis of calls to that subprogram, and it is checked by the tools when
analyzing the body. This level of flow analysis is referred to as information-flow
analysis. As with the other annotations discussed so far, if the
Depends aspect is not provided explicitly for a subprogram then it will be
synthesized by the tools. The synthesized dependency will be a conservative
approximation if the body of the subprogram is not available for analysis,
and may still be an approximation even if the body is available.

.. _Preconditions and Postconditions:

Preconditions and Postconditions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Preconditions and postconditions are very important annotations in |SPARK| as
they enable us to strengthen subprogram contracts by specifying the intended
behaviour in more detail. For example:

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
subprogram entry, and that the postcondition evaluates to ``True`` on
subprogram exit. Their evaluation should also not raise a run-time error, for
example when accessing an array element, or doing arithmetic computations.

When proving a subprogram with |GNATprove|, its precondition is assumed to
hold, and its postcondition is proved. |GNATprove| also generates checks to
prove that the precondition can never raise a run-time error, whatever the
calling context. For example:

.. code-block:: ada
   :linenos:

    function Add (X, Y : Integer) return Integer with
      Pre  => X + Y in Integer,
      Post => Add'Result = X + Y;

    function Get_Value (A : My_Array; J : Index) return Element with
      Pre  => A(J) /= No_Element,
      Post => Add'Result = A(J);

|GNATprove| generates checks to show that ``X + Y`` in the precondition of
``Add`` can never overflow, and that ``A(J)`` in the precondition of ``Get_Value``
can never access ``A`` outside its bounds. These checks cannot be proved. One
can usually rewrite the precondition so that it cannot raise a run-time error,
either by adding a guard in the precondition, or by using a different
formulation that cannot raise a run-time error. For example:

.. code-block:: ada
   :linenos:

    function Add (X, Y : Integer) return Integer with
      Pre  => (if X > 0 and Y > 0 then X <= Integer'Last - Y)
                and then
              (if X < 0 and Y < 0 then X >= Integer'First - Y),
      Post => Add'Result = X + Y;

    function Get_Value (A : My_Array; J : Index) return Element with
      Pre  => J in A'Range and then A(J) /= No_Element,
      Post => Add'Result = A(J);

For overflow checks, an alternate solution exists to avoid them altogether in
annotations, by using unbounded arithmetic in annotations, see :ref:`Overflow
Modes`.

A correct contract may not be sufficient for proof: even if the precondition
and postcondition always evaluate to ``True``, and never raise a run-time
error, they might not be strong enough:

* |GNATprove| analyzes the body of a subprogram in all possible contexts
  allowed by its precondition. The precondition should be strong enough to
  prove that the body is free from run-time errors.

* |GNATprove| proves the postcondition of a subprogram in the context of its
  precondition and body. The precondition should be strong enough to prove the
  postcondition.

* |GNATprove| replaces a call to a subprogram by its contract, asserting its
  precondition and assuming its postcondition. The only information available
  about the call is the callee's postcondition. This postcondition should be
  strong enough to prove the desired properties in the caller.

One can strengthen a contract by making its precondition more restrictive
(accepting less calling contexts) and making its postcondition more precise
(giving more information to prove its callers).

Note that the default precondition (resp. postcondition) of ``True`` used by
|GNATprove| when no explicit one is given may not be strong enough.

Note also that direct recursive subprograms or mutually recursive subprograms
are treated in this respect exactly like non-recursive ones. Provided the
execution of these subprograms always terminates (a property that is not
verified by |GNATprove|), then it is sound to use their contracts at call-site
to prove the same contracts.

.. _Contract Cases:

Contract Cases
^^^^^^^^^^^^^^

The contract of a subprogram can alternatively be specified as a set of
disjoint and complete contract cases:

.. code-block:: ada
   :linenos:

    procedure Incr_Threshold (X : in out Integer) with
      Contract_Cases => (X < Threshold => X = X'Old + 1,
                         X = Threshold => X = X'Old);

Each case in the list consists in a guard and a consequence separated by the
symbol ``=>``. All guards are evaluated on entry to the subprogram. For each
input, only one guard should evaluate to ``True``. The corresponding
consequence should evaluate to ``True`` when returning from the subprogram. For
example, the contract cases of ``Incr_Threshold`` express that the subprogram
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
                or else
              (not (X < Threshold) and X = Threshold),
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

|GNATprove| is able to prove that the contract cases of ``Incr_Threshold`` are
disjoint and complete, even if the case of ``X`` greater than ``Threshold`` is
not considered, because this case is ruled out by the precondition of
``Incr_Threshold``.

Note that the completeness is automatically reached when the last guard is
``others``, denoting all cases that are not captured by any other guard. For
example:

.. code-block:: ada
   :linenos:

    procedure Incr_Threshold (X : in out Integer) with
      Contract_Cases => (X >= 0 and X < Threshold  => X = X'Old + 1,
                         X = Threshold             => X = X'Old,
                         others                    => X = -1;

.. _Refined Postconditions:

Refined Postconditions
^^^^^^^^^^^^^^^^^^^^^^

The postcondition of a subprogram declared in the visible part of a package may
refer to objects of a private type, or to abstract state. In such cases a second,
refined, version of the postcondition may be applied to the subprogram body. This
restates the postcondition in terms of the full view of the private type or the
constituents of the refined state. In fact, a refined postcondition may be given
on the body even if there is no explicit postcondition on the declaration in the
visible part, in which case the postcondition on the declaration defaults to ``True``.

|GNATprove| will attempt to verify that the precondition of the subprogram together
with its refined postcondition imply the postcondition on the declaration (and
a warning will be reported if this cannot be shown to hold).

The example below shows how this might be used in a package which provides a type
for declaring stacks of integers, and operations for that type. In the package
specification the type ``Stack`` is private and the postcondition on procedure ``Push``
states that the stack will not be empty after a push. In the body, where the
type ``Stack`` is fully visible, the refined postcondition gives more detail
about the effect of ``Push``. Note that ``Empty`` is an expression function -
of which we will see more in the next section.

.. code-block:: ada
   :linenos:

   package P is

      type Stack is private;

      function Empty (S : Stack) return Boolean;

      procedure Push (I : in Integer; S : in out Stack)
         with Post => (not Empty (S));

   private
      Stack_Size : constant := 100;
      type Pointer_Range is range 0 .. Stack_Size;
      subtype Stack_Range is Pointer_Range range 1 .. Stack_Size;
      type Stack_Array is array (Stack_Range) of Integer;
      type Stack is record
         Vector  : Stack_Array;
         Pointer : Pointer_Range;
      end record;
   end P;

   package body P is

      function Empty (S : Stack) return Boolean is (S.Pointer = 0);

      procedure Push (I : in Integer; S : in out Stack)
         with Refined_Post => (S.Pointer = S.Pointer'Old + 1)
      is
      begin
         S.Pointer := S.Pointer + 1;
         S.Vector (S.Pointer) := I;
      end Push;

   end P;

.. _Expression Functions:

Expression Functions
^^^^^^^^^^^^^^^^^^^^

Expression functions are functions whose body is an expression, which can be
defined in a spec unit.  Expression functions were introduced in Ada 2012 as a
useful abstraction mechanism for stating properties in preconditions and
postconditions.

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
checks for it. Expression functions that have a user-defined postcondition
are treated like regular functions.

Currently, the knowledge that a function call in an annotation respects
its postcondition (when called in a context where the precondition is
satisfied) is only available for expression functions. Thus, expression
functions should be used whenever possible for these functions called in
annotations.

.. _Ghost Functions:

Ghost Functions
^^^^^^^^^^^^^^^

Sometimes it is useful to declare functions that are needed in annotations only,
but that are intended never to be called in executable code. Such functions may
be used to factor out common parts of expressions in annotations, or to make it
easier to express some desired property to be proved or tested. Such functions
are referred to as ghost functions and their key property is that they have no
effect on the dynamic semantics of the Ada program. If all ghost functions
and references to them in assertions were removed from the source code, the behaviour
of the compiled program would be unchanged.

Ghost functions are identified by the convention ``Ghost`` and may be expression
functions or regular functions. If they are regular functions, then they may be
executable (with a body declared as normal) or non-executable (no body is declared).
If they are non-executable, then they can only be used for proof, not testing, and
their definitions might be provided by an external proof tool in order to complete
the formal verification process.

The examples below show the declarations of the three types of ghost functions
mentioned above.

.. code-block:: ada

   function A_Ghost_Expr_Function (Lo, Hi : Natural) return Natural is
      (if Lo > Integer'Last - Hi then Lo else ((Lo + Hi) / 2))
   with Pre        => Lo <= Hi,
        Post       => A_Ghost_Expr_Function'Result in Lo .. Hi,
        Convention => Ghost;

   function A_Ghost_Function (Lo, Hi : Natural) return Natural
   with Pre        => Lo <= Hi,
        Post       => A_Ghost_Function'Result in Lo .. Hi,
        Convention => Ghost;
   -- The body of the function is declared elsewhere.

   function A_Nonexecutable_Ghost_Function (Lo, Hi : Natural) return Natural
   with Pre        => Lo <= Hi,
        Post       => A_Nonexecutable_Ghost_Function'Result in Lo .. Hi,
        Convention => Ghost,
        Import;
   -- The body of the function is not declared elsewhere.

The |SPARK| tools verify that ghost functions cannot influence any non-ghost
entities in the program.

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
each other, or separated only by ``Loop_Variant`` pragmas).

Internally, |GNATprove| forms a "virtual loop" around these loop
invariants to prove the subprogram. The virtual loop is formed by "unrolling"
the statements preceding the first ``Loop_Invariant`` pragma until it is at
the top of the loop body.

Other ``Loop_Invariant`` pragmas are proved like regular
assertions. Loop invariants may have to be precise enough to prove the property
of interest. For example, in order to prove the postcondition of function
``Contains`` below, one has to write a precise loop invariant such as the one
given below:

.. code-block:: ada
   :linenos:

   type IntArray is array (1 .. 10) of Integer;

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
the value of the variable at loop entry. This can be done using
attribute ``Loop_Entry``. For example, the following procedure
reverses the contents of an array in-place. In order to prove
the postcondition, the loop invariant needs to refer to the original
value of ``A'Loop_Entry`` not the value of ``A`` that has been modified
by earlier iterations of the loop.

.. code-block:: ada
   :linenos:

   procedure Reverse_Order (A : in out IntArray)
      with Post =>
         (for all J in A'Range => A (J) = A'Old (A'Last - J + 1) and
                                  A (A'Last - J + 1) = A'Old (J));

   procedure Reverse_Order (A : in out IntArray)
   is
      Temp : Integer;
   begin
      for Index in A'First .. (A'Last + 1) / 2 loop
         Temp := A (Index);
         A (Index) := A (A'Last - Index + 1);
         A (A'Last - Index + 1) := Temp;
         pragma Loop_Invariant (-- Elements that have visited so far are swapped
                                (for all J in A'First .. Index =>
                                    A (J) = A'Loop_Entry (A'Last - J + 1) and
                                    A (A'Last - J + 1) = A'Loop_Entry (J))
                                   and then
                                   -- Elements not yet visited are unchanged
                                   (for all J in Index + 1 .. A'Last - Index =>
                                       A (J) = A'Loop_Entry (J)));

      end loop;
   end Reverse_Order;


Note in particular the second conjunct in the loop invariant, which states the
elements of ``A`` that have not yet been swapped. This part of an invariant
or contract stating what has not been
modified, called in the scientific literature the *frame condition*, is essential for
|GNATprove| to work effectively. Special care should be taken to write adequate
frame conditions, as they usually look obvious to programmers, and so it is
very common to forget to write them.

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
|GNATprove|, as they become loop variants of the underlying virtual loop. Other
``Loop_Variant`` pragmas are proved by showing that the quantity that should
progress monotonically does so between the program point where the first group
of ``Loop_Invariant`` pragmas appears (or the start of the loop if there is no
such group) and the program point where the ``Loop_Variant`` pragma appears,
and that this quantity either stays the same or progresses on the rest of the
loop.

Quantified Expressions
----------------------

Ada 2012 quantified expressions are a special case with respect to run-time
errors: the enclosed expression must be run-time error free over the *entire
range* of the quantification, not only at points that would actually be
reached at execution. As an example, consider the following expression:

.. code-block:: ada

    (for all I in 1 .. 10 => 1 / (I - 3) > 0)

This quantified expression will never raise a run-time error, because the test
is already false for the first value of the range, ``I = 1``, and the execution
will stop, with the result value ``False``. However, |GNATprove| requires the
expression to be run-time error free over the entire range, including ``I =
3``, so there will be an unproved check for the division by zero in this case.

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

.. _Overflow Modes:

Overflow Modes
--------------

Annotations such as preconditions, postconditions, assertions, loop invariants,
are analyzed by |GNATprove| with the exact same meaning that they have during
execution. In particular, evaluating the expressions in an annotation may raise
a run-time error, in which case |GNATprove| will attempt to prove that this
error cannot occur, and report a warning otherwise.

Integer overflows are a kind of run-time error that occurs when the result of
an arithmetic computation does not fit in the bounds of the machine type used
to hold the result. In some cases, it is convenient to express properties in
annotations as they would be expressed in mathematics, where quantities are
unbounded, for example:

.. code-block:: ada
   :linenos:

    function Add (X, Y : Integer) return Integer with
      Pre  => X + Y in Integer,
      Post => Add'Result = X + Y;

The precondition of ``Add`` states that the result of adding its two parameters
should fit in type ``Integer``. In the default mode, evaluating this expression
will fail an overflow check, because the result of ``X + Y`` is stored in a
temporary of type ``Integer``. If the compilation switch ``-gnato13`` is used,
then annotations are compiled specially, so that arithmetic operations use
unbounded intermediate results. In this mode, |GNATprove| does not generate a
check for the addition of ``X`` and ``Y`` in the precondition of ``Add``, as
there is no possible overflow here.

There are three overflow modes:

* Use base type for intermediate operations (STRICT): in this mode, all
  intermediate results for predefined arithmetic operators are computed using
  the base type, and the result must be in range of the base type.
* Most intermediate overflows avoided (MINIMIZED): in this mode, the compiler
  attempts to avoid intermediate overflows by using a larger integer type,
  typically Long_Long_Integer, as the type in which arithmetic is performed
  for predefined arithmetic operators.
* All intermediate overflows avoided (ELIMINATED): in this mode, the compiler
  avoids all intermediate overflows by using arbitrary precision arithmetic as
  required.

The desired mode of for handling intermediate overflow can be specified using
either the Overflow_Mode pragma or an equivalent compiler switch. The pragma
has the form::

    pragma Overflow_Mode ([General =>] MODE [, [Assertions =>] MODE]);

where MODE is one of

* STRICT: intermediate overflows checked (using base type)
* MINIMIZED: minimize intermediate overflows
* ELIMINATED: eliminate intermediate overflows

For example:

.. code-block:: ada

   pragma Overflow_Mode (General => Strict, Assertions => Eliminated);

specifies that general expressions outside assertions be evaluated in the usual
strict mode, and expressions within assertions be evaluated in "eliminate
intermediate overflows" mode. Currently, GNATprove only supports pragma
``Overflow_Mode`` being specified in a configuration pragma file.

Additionally, a compiler switch ``-gnato??`` can be used to control the
checking mode default. Here `?` is one of the digits `1` through `3`:

#. use base type for intermediate operations (STRICT)
#. minimize intermediate overflows (MINIMIZED)
#. eliminate intermediate overflows (ELIMINATED)

The switch ``-gnato13``, like the ``Overflow_Mode`` pragma above, specifies that
general expressions outside assertions be evaluated in the usual strict mode,
and expressions within assertions be evaluated in "eliminate intermediate
overflows" mode.

Note that these modes apply only to the evaluation of predefined arithmetic,
membership, and comparison operators for signed integer arithmetic.

For further details of the meaning of these modes, and for further information
about the treatment of overflows for fixed-point and floating-point arithmetic
please refer to the "Overflow Check Handling in GNAT" appendix in the |GNAT Pro|
User's Guide.

|SPARK| Libraries
=================

Formal Containers Library
-------------------------

Containers are generic data structures offering a high-level view of
collections of objects, while guaranteeing fast access to their
content to retrieve or modify it. The most common containers are
lists, vectors, sets and maps, which are defined in Ada Standard
Libraries. In critical software where verification objectives
severely restrict the use of pointers, containers offer an attractive
alternative to pointer-intensive data structures.

There are 6 formal containers, which are part of the GNAT standard
library:

* ``Ada.Containers.Formal_Vectors``
* ``Ada.Containers.Formal_Doubly_Linked_Lists``
* ``Ada.Containers.Formal_Hashed_Sets``
* ``Ada.Containers.Formal_Ordered_Sets``
* ``Ada.Containers.Formal_Hashed_Maps``
* ``Ada.Containers.Formal_Ordered_Maps``

They are adapted to critical software
development. They are bounded, so that there can be no dynamic
allocation and they have preconditions that can be used to ensure that
there is no error at run-time. They are experimental, and, as such,
should be used with care. In particular, the examples below can be
compiled and fed to |GNATprove| but not everything is proved about them in a
reasonable amount of time.

Specification of formal containers is in |SPARK|. As a consequence,
there is no procedure that take a procedure as an argument such that
``Update_Element`` or ``Query_Element`` in Ada Standard container
library.

Formal containers are adapted to the specification process. First of all,
cursors no longer have a reference to underlying container. Indeed, in Ada
Standard container library, cursors contain a pointer to their underlying
container. As a consequence, if a container is modified, then so are all
cursors attached to this container, which is contrary to the philosophy of
modular verification in |SPARK|, hence the modification to separate cursors
from containers. This modification also allows to use the same cursor with
different containers. In particular, it is useful to link elements associated
to a list before and after a modification. Formal containers also provide three
new functions per container type. ``Current_To_Last (C : Container; Cu : Cursor)
returns Container`` and ``First_To_Previous (C : Container; Cu : Cursor) returns
Container`` can be used to write loop invariant. They return the trailing
(resp. the leading) part of the container ``C`` starting before
(resp. stopping before) the cursor ``Cu``.

For example, in the function ``My_Find`` below, ``First_To_Previous`` is used in the
loop invariant to state that the element ``E`` has not been found in
the part of the list that as been analyzed already.

.. code-block:: ada
   :linenos:

   function My_Find (L : List; E : Element_Type) return Cursor with
     Post => (if My_Find'Result = No_Element then
                not Contains (L, E)
              else (Has_Element (L, My_Find'Result)
                     and then
                    Element (L, My_Find'Result) = E));

.. code-block:: ada
   :linenos:

   function My_Find (L : List; E : Element_Type) return Cursor is
      Cu : Cursor := First (L);
   begin
      while Has_Element (L, Cu) loop
         pragma Loop_Invariant (not Contains (First_To_Previous (L, Cu), E));
         if Element (L, Cu) = E then
            return Cu;
         end if;
         Next (L, Cu);
      end loop;
      return No_Element;
   end My_Find;

The third new function,
``Strict_Equal (C1, C2 : Container)`` checks whether ``C1`` and ``C2``
really are equal with respect to everything that can impact existing
functions of the library. On lists for example, it does not only check
that ``C1`` and ``C2`` contain the same elements in the same order but
also that ``C1`` and ``C2`` share the same cursors. This function is
generaly used for stating which parts of a container do not change in a
loop invariant or a postcondition.

Note that the model of ``Strict_Equal`` uses the theoretical equality
on elements whereas its implementation uses the parameter ``=``
of the generic to compare elements. This is done so that the function
``Strict_Equal`` can always be used to express invariant properties of
collections over loops and calls.
This difference between proof and test means that, when the parameter
``=`` used to instantiate a generic formal container
is not the physical equality on elements, a
user should be careful not to use testing to discharge
assumptions involving ``Strict_Equal``, such as preconditions of
proven subprograms and postconditions of programs called by a
proven subprogram, which mention ``Strict_Equal``.

For example, in the function ``My_Prepend`` below, ``Strict_Equal`` is
used to state that ``My_Prepend`` does not modify the tail of the
list. Note that we use ``First (L1'Old)`` to refer to the first
element of the tail in the postcondition of ``My_Prepend``, which would not have
been possible if cursors still had an internal reference to the list
they come from.

.. code-block:: ada
   :linenos:

   procedure My_Prepend (L1 : in out List; E : Element_Type) with
     Pre  => L1.Capacity > Length (L1),
     Post => Length (L1) = 1 + Length (L1'Old)
               and then First_Element (L1) = E
               and then Strict_Equal (Current_To_Last(L1, First (L1'Old)), L1'Old);

Quantification over Containers
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The Ada 2012 language  provides quantified expressions that can be used to express a property over a standard container.
For example, that all elements of a list of integers are prime, which can be expressed by iterating over cursors as follows:

.. code-block:: ada

   (for all Cu in My_List => Is_Prime (Element (Cu)))

The general mechanism in Ada 2012 that provides this functionality relies on the use of tagged types (for the container type) and various aspects involving access types, so cannot be applied to the SPARK formal containers.

Instead, formal containers are annotated with an aspect named Iterable that provides the same functionality in a simpler way, leading also to much simpler object code. For example, here is the definition of the type ``List`` for doubly linked lists:

.. code-block:: ada

   type List (Capacity : Count_Type) is private
     with Iterable => (First       => First,
                       Has_Element => Has_Element,
                       Next        => Next,
                       Element     => Element);

Thanks to this mechanism, one can use a quantified expression to express that all elements of a formal list of integers are prime:

.. code-block:: ada

   (for all Cu in My_List => Is_Prime (Element (My_List, Cu)))

The compiler will generate code that iterates over ``My_List`` using the functions ``First``, ``Has_Element`` and ``Next`` given in the Iterable aspect, so that the above is equivalent to:

.. code-block:: ada
   :linenos:

   declare
     Cu     : Cursor_Type := First (My_List);
     Result : Boolean := True;
   begin
     while Result and then Has_Element (My_List, Cu) loop
       Result := Is_Prime (Element (My_List, Cu));
       Cu     := Next (My_List, Cu);
     end loop;
   end;

where ``Result`` is the value of the quantified expression.

Mixing |SPARK| Code and Ada Code
================================

An Ada program unit or other construct is said to be "in |SPARK|"
if it complies with the restrictions required to permit formal verification
given  in the |SPARK| Reference Manual.
Conversely, an Ada program unit or other construct is "not in |SPARK|" if
it does not meet these requirements, and so is not amenable to formal
verification.

Within a single Ada unit, constructs which are "in" and "not in" |SPARK| may be
mixed at a fine level in accordance with the following two general principles:

- SPARK code shall only reference SPARK declarations, but a SPARK
  declaration which requires a completion may have a non-SPARK completion.

- SPARK code shall only enclose SPARK code, except that SPARK code
  may enclose a non-SPARK completion of an enclosed SPARK declaration.

More specifically, non-SPARK completions of SPARK declarations are allowed
for subprogram declarations, package declarations, private type declarations,
and deferred constant declarations. [When tagged types are
fully supported in |SPARK|, this list will also include private extension
declarations.] [Strictly speaking, a package's private part is considered
to be part of its completion for purposes of the above rules; this is
described in more detail below].

When a non-SPARK completion is provided for a SPARK declaration, the
user has an obligation to ensure that the non-SPARK completion
is consistent (with respect to the semantics of |SPARK|) with its SPARK
declaration. For example, |SPARK| requires that a function call has no
side effects. If the body of a given function is in |SPARK|, then this
rule is enforced via various language rules; otherwise, it is the
responsibility of the user to ensure that the function body does not
violate this rule. As with other
such constructs (notably pragma Assume), failure to meet this obligation
can invalidate any or all analysis (i.e., proofs and/or flow analysis)
associated with the SPARK portion of a program. A non-SPARK completion
meets this obligation if it is semantically equivalent (with respect to
dynamic semantics) to some notional completion that could have been
written in |SPARK|.

The |SPARK| semantics (specifically including flow analysis and proofs) of
a "mixed" program which meets the aforementioned requirement is well defined -
it is the semantics of the equivalent 100% |SPARK| program.
For the semantics of other "mixed" programs, go look in the Ada Reference
Manual.

In the case of a package, the specification/completion division described
above is a simplification of the true situation. A package is divided into
4 sections, not just 2: its visible part, its private part, the declarations
of its body, and the statement list of its body. For a given package and
any number N in the range 0 .. 4, the first N sections of the package might
be in |SPARK| while the remainder is not.

For example, the following combinations may be typical:

- Package specification in |SPARK|. Package body not in |SPARK|.

- Visible part of package specification in |SPARK|. Private part and body not
  in |SPARK|.

- Package specification in |SPARK|. Package body almost entirely in |SPARK|,
  with a small number of subprogram bodies not in |SPARK|.

- Package specification in |SPARK|, with all subprogram bodies imported
  from another language.

- Package specification contains a mixture of declarations which are in |SPARK|
  and not in |SPARK|.  The latter declarations are only visible and usable from
  client units which are not in |SPARK|.

Such patterns are intended to allow for application of formal verification to a
subset of a program, and the combination of formal verification with more
traditional testing (see :ref:`proof and test`).
