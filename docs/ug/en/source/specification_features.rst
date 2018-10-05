.. _Specification Features:

Specification Features
======================

|SPARK| contains many features for specifying the intended behavior of
programs. Some of these features come from Ada 2012 (:ref:`Attribute Old` and
:ref:`Expression Functions` for example). Other features are specific to
|SPARK| (:ref:`Attribute loop_Entry` and :ref:`Ghost Code` for example). In
this section, we describe these features and their impact on execution and
formal verification.

.. _Aspect Constant_After_Elaboration:

Aspect ``Constant_After_Elaboration``
-------------------------------------

Aspect ``Constant_After_Elaboration`` can be specified on a library level
variable that has an initialization expression. When specified, the
corresponding variable can only be changed during the elaboration of its
enclosing package. |SPARK| ensures that users of the package do not change the
variable. This feature can be particularly useful in tasking code since
variables that are Constant_After_Elaboration are guaranteed to prevent
unsynchronized modifications (see :ref:`Tasks and Data Races`).

.. code-block:: ada

   package CAE is
      Var : Integer := 0 with
        Constant_After_Elaboration;

      --  The following is illegal because users of CAE could call Illegal
      --  and that would cause an update of Var after CAE has been
      --  elaborated.
      procedure Illegal with
         Global => (Output => Var);
   end CAE;

   package body CAE is
      procedure Illegal is
      begin
         Var := 10;
      end Illegal;

      --  The following subprogram is legal because it is declared inside
      --  the body of CAE and therefore it cannot be directly called
      --  from a user of CAE.
      procedure Legal is
      begin
         Var := Var + 2;
      end Legal;

   begin
      --  The following statements are legal since they take place during
      --  the elaboration of CAE.
      Var := Var + 1;
      Legal;
   end CAE;

.. _Attribute Old:

Attribute ``Old``
-----------------

[Ada 2012]

In a Postcondition
^^^^^^^^^^^^^^^^^^

Inside :ref:`Postconditions`, attribute ``Old`` refers to the values that
expressions had at subprogram entry. For example, the postcondition of
procedure ``Increment`` might specify that the value of parameter ``X`` upon
returning from the procedure has been incremented:

.. code-block:: ada

   procedure Increment (X : in out Integer) with
     Post => X = X'Old + 1;

At run time, a copy of the variable ``X`` is made when entering the
subprogram. This copy is then read when evaluating the expression ``X'Old`` in
the postcondition. Because it requires copying the value of ``X``, the type of
``X`` cannot be limited.

Strictly speaking, attribute ``Old`` must apply to a *name* in Ada syntax, for
example a variable, a component selection, a call, but not an addition like
``X + Y``. For expressions that are not *names*, attribute ``Old`` can be applied
to their qualified version, for example:

.. code-block:: ada

   procedure Increment_One_Of (X, Y : in out Integer) with
     Post => X + Y = Integer'(X + Y)'Old + 1;

Because the compiler unconditionally creates a copy of the expression to which
attribute ``Old`` is applied at subprogram entry, there is a risk that this feature
might confuse users in more complex postconditions. Take the example of a
procedure ``Extract``, which copies the value of array ``A`` at index ``J`` into
parameter ``V``, and zeroes out this value in the array, but only if ``J`` is
in the bounds of ``A``:

.. code-block:: ada

   procedure Extract (A : in out My_Array; J : Integer; V : out Value) with
     Post => (if J in A'Range then V = A(J)'Old);  --  INCORRECT

Clearly, the value of ``A(J)`` at subprogram entry is only meaningful if ``J``
is in the bounds of ``A``. If the code above was allowed, then a copy of
``A(J)`` would be made on entry to subprogram ``Extract``, even when ``J`` is
out of bounds, which would raise a run-time error. To avoid this common
pitfall, use of attribute ``Old`` in expressions that are potentially unevaluated
(like the then-part in an if-expression, or the right argument of a shortcut
boolean expression - See Ada RM 6.1.1) is restricted to
plain variables: ``A`` is allowed, but not ``A(J)``. The |GNAT Pro| compiler
issues the following error on the code above::

   prefix of attribute "Old" that is potentially unevaluated must denote an entity

The correct way to specify the postcondition in the case above is to apply
attribute ``Old`` to the entity prefix ``A``:

.. code-block:: ada

   procedure Extract (A : in out My_Array; J : Integer; V : out Value) with
     Post => (if J in A'Range then V = A'Old(J));

In Contract Cases
^^^^^^^^^^^^^^^^^

The rule for attribute ``Old`` inside :ref:`Contract Cases` is more
permissive. Take for example the same contract as above for procedure
``Extract``, expressed with contract cases:

.. code-block:: ada

   procedure Extract (A : in out My_Array; J : Integer; V : out Value) with
     Contract_Cases => ((J in A'Range) => V = A(J)'Old,
                        others         => True);

Only the expressions used as prefixes of attribute ``Old`` in the *currently
enabled case* are copied on entry to the subprogram. So if ``Extract`` is
called with ``J`` out of the range of ``A``, then the second case is enabled,
so ``A(J)`` is not copied when entering procedure ``Extract``. Hence, the above
code is allowed.

It may still be the case that some contracts refer to the value of objects at
subprogram entry inside potentially unevaluated expressions. For example, an
incorrect variation of the above contract would be:

.. code-block:: ada

   procedure Extract (A : in out My_Array; J : Integer; V : out Value) with
     Contract_Cases => (J >= A'First => (if J <= A'Last then V = A(J)'Old),  --  INCORRECT
                        others       => True);

For the same reason that such uses are forbidden by Ada RM inside
postconditions, the SPARK RM forbids these uses inside contract cases (see
SPARK RM 6.1.3(2)). The |GNAT Pro| compiler issues the following error on the code
above::

   prefix of attribute "Old" that is potentially unevaluated must denote an entity

The correct way to specify the consequence expression in the case above is to
apply attribute ``Old`` to the entity prefix ``A``:

.. code-block:: ada

   procedure Extract (A : in out My_Array; J : Integer; V : out Value) with
     Contract_Cases => (J >= A'First => (if J <= A'Last then V = A'Old(J)),
                        others       => True);

.. _In a Potentially Unevaluated Expression:

In a Potentially Unevaluated Expression
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In some cases, the compiler issues the error discussed above (on attribute ``Old``
applied to a non-entity in a potentially unevaluated context) on an expression
that can safely be evaluated on subprogram entry, for example:

.. code-block:: ada

   procedure Extract (A : in out My_Array; J : Integer; V : out Value) with
     Post => (if J in A'Range then V = Get_If_In_Range(A,J)'Old);  --  ERROR

where function ``Get_If_In_Range`` returns the value ``A(J)`` when ``J`` is in
the bounds of ``A``, and a default value otherwise.

In that case, the solution is either to rewrite the postcondition using
non-shortcut boolean operators, so that the expression is not *potentially
evaluated* anymore, for example:

.. code-block:: ada

   procedure Extract (A : in out My_Array; J : Integer; V : out Value) with
     Post => J not in A'Range or V = Get_If_In_Range(A,J)'Old;

or to rewrite the postcondition using an intermediate expression function, so
that the expression is not *potentially evaluated* anymore, for example:

.. code-block:: ada

   function Extract_Post (A : My_Array; J : Integer; V, Get_V : Value) return Boolean is
     (if J in A'Range then V = Get_V);

   procedure Extract (A : in out My_Array; J : Integer; V : out Value) with
     Post => Extract_Post (A, J, V, Get_If_In_Range(A,J)'Old);

or to use the |GNAT Pro| pragma ``Unevaluated_Use_Of_Old`` to allow such uses
of attribute ``Old`` in potentially unevaluated expressions:

.. code-block:: ada

   pragma Unevaluated_Use_Of_Old (Allow);

   procedure Extract (A : in out My_Array; J : Integer; V : out Value) with
     Post => (if J in A'Range then V = Get_If_In_Range(A,J)'Old);

|GNAT Pro| does not issue an error on the code above, and always evaluates the
call to ``Get_If_In_Range`` on entry to procedure ``Extract``, even if this
value may not be used when executing the postcondition. Note that the formal
verification tool |GNATprove| correctly generates all required checks to prove
that this evaluation on subprogram entry does not fail a run-time check or a
contract (like the precondition of ``Get_If_In_Range`` if any).

Pragma ``Unevaluated_Use_Of_Old`` applies to uses of attribute ``Old`` both
inside postconditions and inside contract cases. See |GNAT Pro| RM for a
detailed description of this pragma.

.. _Attribute Result:

Attribute ``Result``
--------------------

[Ada 2012]

Inside :ref:`Postconditions` of functions, attribute ``Result`` refers to the
value returned by the function. For example, the postcondition of function
``Increment`` might specify that it returns the value of parameter ``X`` plus
one:

.. code-block:: ada

   function Increment (X : Integer) return Integer with
     Post => Increment'Result = X + 1;

Contrary to ``Attribute Old``, attribute ``Result`` does not require copying
the value, hence it can be applied to functions that return a limited
type. Attribute ``Result`` can also be used inside consequence expressions in
:ref:`Contract Cases`.

.. _Attribute Loop_Entry:

Attribute ``Loop_Entry``
------------------------

[|SPARK|]

It is sometimes convenient to refer to the value of variables at loop entry. In
many cases, the variable has not been modified between the subprogram entry and
the start of the loop, so this value is the same as the value at subprogram
entry. But :ref:`Attribute Old` cannot be used in that case. Instead, we can
use attribute ``Loop_Entry``. For example, we can express that after ``J``
iterations of the loop, the value of parameter array ``X`` at index ``J`` is
equal to its value at loop entry plus one:

.. code-block:: ada

   procedure Increment_Array (X : in out Integer_Array) is
   begin
      for J in X'Range loop
         X(J) := X(J) + 1;
         pragma Assert (X(J) = X'Loop_Entry(J) + 1);
      end loop
   end Increment_Array;

At run time, a copy of the variable ``X`` is made when entering the loop. This
copy is then read when evaluating the expression ``X'Loop_Entry``. No copy is
made if the loop is never entered. Because it requires copying the value of
``X``, the type of ``X`` cannot be limited.

Attribute ``Loop_Entry`` can only be used in top-level :ref:`Assertion Pragmas`
inside a loop. It is mostly useful for expressing complex :ref:`Loop
Invariants` which relate the value of a variable at a given iteration of the
loop and its value at loop entry. For example, we can express that after ``J``
iterations of the loop, the value of parameter array ``X`` at all indexes
already seen is equal to its value at loop entry plus one, and that its value
at all indexes not yet seen is unchanged, using :ref:`Quantified Expressions`:

.. code-block:: ada

   procedure Increment_Array (X : in out Integer_Array) is
   begin
      for J in X'Range loop
         X(J) := X(J) + 1;
         pragma Loop_Invariant (for all K in X'First .. J => X(K) = X'Loop_Entry(K) + 1);
         pragma Loop_Invariant (for all K in J + 1 .. X'Last => X(K) = X'Loop_Entry(K));
      end loop;
   end Increment_Array;

Attribute ``Loop_Entry`` may be indexed by the name of the loop to which it
applies, which is useful to refer to the value of a variable on entry to an
outter loop. When used without loop name, the attribute applies to the closest
enclosing loop. For examples, ``X'Loop_Entry`` is the same as
``X'Loop_Entry(Inner)`` in the loop below, which is not the same as
``X'Loop_Entry(Outter)`` (although all three assertions are true):

.. code-block:: ada

   procedure Increment_Matrix (X : in out Integer_Matrix) is
   begin
      Outter: for J in X'Range(1) loop
         Inner: for K in X'Range(2) loop
            X(J,K) := X(J,K) + 1;
            pragma Assert (X(J,K) = X'Loop_Entry(J,K) + 1);
            pragma Assert (X(J,K) = X'Loop_Entry(Inner)(J,K) + 1);
            pragma Assert (X(J,K) = X'Loop_Entry(Outter)(J,K) + 1);
         end loop Inner;
      end loop Outter;
   end Increment_Matrix;

By default, similar restrictions exist for the use of attribute ``Loop_Entry``
and the use of attribute ``Old`` :ref:`In a Potentially Unevaluated
Expression`. The same solutions apply here, in particular the use of |GNAT Pro|
pragma ``Unevaluated_Use_Of_Old``.

.. _Attribute Update:

Attribute ``Update``
--------------------

[|SPARK|]

It is quite common in :ref:`Postconditions` to relate the input and output
values of parameters. While this can be as easy as ``X = X'Old + 1`` in the
case of scalar parameters, it is more complex to express for array and record
parameters. Attribute ``Update`` is useful in that case, to denote the updated
value of a composite variable. For example, we can express more clearly that
procedure ``Zero_Range`` zeroes out the elements of its array parameter ``X``
between ``From`` and ``To`` by using attribute ``Update``:

.. code-block:: ada

   procedure Zero_Range (X : in out Integer_Array; From, To : Positive) with
     Post => X = X'Old'Update(From .. To => 0);

than with an equivalent postcondition using :ref:`Quantified Expressions` and
:ref:`Conditional Expressions`:

.. code-block:: ada

   procedure Zero_Range (X : in out Integer_Array; From, To : Positive) with
     Post => (for all J in X'Range =>
                (if J in From .. To then X(J) = 0 else X(J) = X'Old(J)));

Attribute ``Update`` takes in argument a list of associations between indexes
(for arrays) or components (for records) and values. Components can only be
mentioned once, with the semantics that all values are evaluated before any
update. Array indexes may be mentioned more than once, with the semantics that
updates are applied in left-to-right order. For example, the postcondition of
procedure ``Swap`` expresses that the values at indexes ``J`` and ``K`` in
array ``X`` have been swapped:

.. code-block:: ada

   procedure Swap (X : in out Integer_Array; J, K : Positive) with
     Post => X = X'Old'Update(J => X'Old(K), K => X'Old(J));

and the postcondition of procedure ``Rotate_Clockwize_Z`` expresses that the
point ``P`` given in parameter has been rotated 90 degrees clockwise around the
Z axis (thus component ``Z`` is preserved while components ``X`` and ``Y`` are
modified):

.. code-block:: ada

   procedure Rotate_Clockwize_Z (P : in out Point_3D) with
     Post => P = P'Old'Update(X => P.Y'Old, Y => - P.X'Old);

Similarly to its use in combination with attribute ``Old`` in postconditions,
attribute ``Update`` is useful in combination with :ref:`Attribute Loop_Entry`
inside :ref:`Loop Invariants`. For example, we can express the property that,
after iteration ``J`` in the main loop in procedure ``Zero_Range``, the value
of parameter array ``X`` at all indexes already seen is equal to zero:

.. code-block:: ada

   procedure Zero_Range (X : in out Integer_Array; From, To : Positive) is
   begin
      for J in From .. To loop
         X(J) := 0;
         pragma Loop_Invariant (X = X'Loop_Entry'Update(From .. J => 0));
      end loop;
   end Zero_Range;

Attribute ``Update`` can also be used outside of assertions. It is particularly
useful in expression functions. For example, the functionality in procedure
``Rotate_Clockwize_Z`` could be expressed equivalently as an expression
function:

.. code-block:: ada

   function Rotate_Clockwize_Z (P : Point_3D) return Point_3D is
     (P'Update(X => P.Y, Y => - P.X));

Because it requires copying the value of ``P``, the type of ``P`` cannot be
limited.

.. _Conditional Expressions:

Conditional Expressions
-----------------------

[Ada 2012]

A conditional expression is a way to express alternative possibilities in an
expression. It is like the ternary conditional expression ``cond ? expr1 :
expr2`` in C or Java, except more powerful. There are two kinds of conditional
expressions in Ada:

* if-expressions are the counterpart of if-statements in expressions
* case-expressions are the counterpart of case-statements in expressions

For example, consider the variant of procedure ``Add_To_Total`` seen in
:ref:`Contract Cases`, which saturates at a given threshold. Its postcondition
can be expressed with an if-expression as follows:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Post => (if Total'Old + Incr < Threshold  then
                Total = Total'Old + Incr
              else
                Total = Threshold);

Each branch of an if-expression (there may be one, two or more branches when
``elsif`` is used) can be seen as a logical implication, which explains why the
above postcondition can also be written:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Post => (if Total'Old + Incr < Threshold then Total = Total'Old + Incr) and
             (if Total'Old + Incr >= Threshold then Total = Threshold);

or equivalently (as the absence of ``else`` branch above is implicitly the same
as ``else True``):

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Post => (if Total'Old + Incr < Threshold then Total = Total'Old + Incr else True) and
             (if Total'Old + Incr >= Threshold then Total = Threshold else True);

If-expressions are not necessarily of boolean type, in which case they must
have an ``else`` branch that gives the value of the expression for cases not
covered in previous conditions (as there is no implicit ``else True`` in such
a case). For example, here is a postcondition equivalent to the above, that
uses an if-expression of ``Integer`` type:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Post => Total = (if Total'Old + Incr < Threshold then Total'Old + Incr else Threshold);

Although case-expressions can be used to cover cases of any scalar type, they
are mostly used with enumerations, and the compiler checks that all cases are
disjoint and that together they cover all possible cases. For example, consider
a variant of procedure ``Add_To_Total`` which takes an additional ``Mode``
global input of enumeration value ``Single``, ``Double``, ``Negate`` or
``Ignore``, with the intuitive corresponding leverage effect on the
addition. The postcondition of this variant can be expressed using a
case-expression as follows:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Post => (case Mode is
                when Single => Total = Total'Old + Incr,
                when Double => Total = Total'Old + 2 * Incr,
                when Ignore => Total = Total'Old,
                when Negate => Total = Total'Old - Incr);

Like if-expressions, case-expressions are not necessarily of boolean type. For
example, here is a postcondition equivalent to the above, that uses a
case-expression of ``Integer`` type:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Post => Total = Total'Old + (case Mode is
                                    when Single => Incr,
                                    when Double => 2 * Incr,
                                    when Ignore => 0,
                                    when Negate => - Incr);

A last case of ``others`` can be used to denote all cases not covered by
previous conditions. If-expressions and case-expressions should always be
parenthesized.

.. _Quantified Expressions:

Quantified Expressions
----------------------

[Ada 2012]

A quantified expression is a way to express a property over a collection,
either an array or a container (see :ref:`Formal Containers Library`):

* a `universally quantified expression` using ``for all`` expresses a property
  that holds for all elements of a collection
* an `existentially quantified expression` using ``for some`` expresses a
  property that holds for at least one element of a collection

For example, consider the procedure ``Increment_Array`` that increments each
element of its array parameter ``X`` by one. Its postcondition can be expressed
using a universally quantified expression as follows:

.. code-block:: ada

   procedure Increment_Array (X : in out Integer_Array) with
     Post => (for all J in X'Range => X(J) = X'Old(J) + 1);

The negation of a universal property being an existential property (the
opposite is true too), the postcondition above can be expressed also using an
existentially quantified expression as follows:

.. code-block:: ada

   procedure Increment_Array (X : in out Integer_Array) with
     Post => not (for some J in X'Range => X(J) /= X'Old(J) + 1);

At run time, a quantified expression is executed like a loop, which exits as
soon as the value of the expression is known: if the property does not hold
(resp. holds) for a given element of a universally (resp. existentially)
quantified expression, execution of the loop does not proceed with remaining
elements and returns the value ``False`` (resp. ``True``) for the expression.

When a quantified expression is analyzed with |GNATprove|, it uses the logical
counterpart of the quantified expression. |GNATprove| also checks that the
expression is free from run-time errors. For this checking, |GNATprove| checks
that the enclosed expression is free from run-time errors over the *entire
range* of the quantification, not only at points that would actually be reached
at run time. As an example, consider the following expression:

.. code-block:: ada

    (for all I in 1 .. 10 => 1 / (I - 3) > 0)

This quantified expression cannot raise a run-time error, because the enclosed
expression ``1 / (I - 3) > 0`` is false for the first value of the range ``I =
1``, so the execution of the loop exits immediately with the value ``False``
for the quantified expression. |GNATprove| is stricter and requires the
enclosed expression ``1 / (I - 3) > 0`` to be free from run-time errors over
the entire range ``I in 1 .. 10`` (including ``I = 3``) so it issues a check
message for a possible division by zero in this case.

Quantified expressions should always be parenthesized.

.. _Expression Functions:

Expression Functions
--------------------

[Ada 2012]

An expression function is a function whose implementation is given by a single
expression. For example, the function ``Increment`` can be defined as an
expression function as follows:

.. code-block:: ada

   function Increment (X : Integer) return Integer is (X + 1);

For compilation and execution, this definition is equivalent to:

.. code-block:: ada

   function Increment (X : Integer) return Integer is
   begin
      return X + 1;
   end Increment;

For |GNATprove|, this definition as expression function is equivalent to the
same function body as above, plus a postcondition:

.. code-block:: ada

   function Increment (X : Integer) return Integer with
     Post => Increment'Result = X + 1
   is
   begin
      return X + 1;
   end Increment;

Thus, a user does not need in general to add a postcondition to an expression
function, as the implicit postcondition generated by |GNATprove| is the most
precise one. If a user adds a postcondition to an expression function,
|GNATprove| uses this postcondition to analyze the function's callers as well
as the most precise implicit postcondition.

On the contrary, it may be useful in general to add a precondition to an
expression function, to constrain the contexts in which it can be called. For
example, parameter ``X`` passed to function ``Increment`` should be less than
the maximal integer value, otherwise an overflow would occur. We can specify
this property in ``Increment``'s precondition as follows:

.. code-block:: ada

   function Increment (X : Integer) return Integer is (X + 1) with
     Pre => X < Integer'Last;

Note that the contract of an expression function follows its expression.

Expression functions can be defined in package declarations, hence they are
well suited for factoring out common properties that are referred to in
contracts. For example, consider the procedure ``Increment_Array`` that
increments each element of its array parameter ``X`` by one. Its precondition
can be expressed using expression functions as follows:

.. code-block:: ada

   package Increment_Utils is

      function Not_Max (X : Integer) return Boolean is (X < Integer'Last);

      function None_Max (X : Integer_Array) return Boolean is
        (for all J in X'Range => Not_Max (X(J)));

      procedure Increment_Array (X : in out Integer_Array) with
        Pre => None_Max (X);

   end Increment_Utils;

Expression functions can be defined over private types, and still be used in
the contracts of publicly visible subprograms of the package, by declaring the
function publicly and defining it in the private part. For example:

.. code-block:: ada

   package Increment_Utils is

      type Integer_Array is private;

      function None_Max (X : Integer_Array) return Boolean;

      procedure Increment_Array (X : in out Integer_Array) with
        Pre => None_Max (X);

   private

      type Integer_Array is array (Positive range <>) of Integer;

      function Not_Max (X : Integer) return Boolean is (X < Integer'Last);

      function None_Max (X : Integer_Array) return Boolean is
        (for all J in X'Range => Not_Max (X(J)));

   end Increment_Utils;

If an expression function is defined in a unit spec, |GNATprove| can use its
implicit postcondition at every call. If an expression function is defined in a
unit body, |GNATprove| can use its implicit postcondition at every call in the
same unit, but not at calls inside other units. This is true even if the
expression function is declared in the unit spec and defined in the unit body.

.. _Ghost Code:

Ghost Code
----------

[|SPARK|]

Sometimes, the variables and functions that are present in a program are not
sufficient to specify intended properties and to verify these properties with
|GNATprove|. In such a case, it is possible in |SPARK| to insert in the program
additional code useful for specification and verification, specially identified
with the aspect ``Ghost`` so that it can be discarded during
compilation. So-called `ghost code` in |SPARK| are these parts of the code that
are only meant for specification and verification, and have no effect on the
functional behavior of the program.

Various kinds of ghost code are useful in different situations:

* `Ghost functions` are typically used to express properties used in contracts.
* `Global ghost variables` are typically used to keep track of the current
  state of a program, or to maintain a log of past events of some type. This
  information can then be referred to in contracts.
* `Local ghost variables` are typically used to hold intermediate values during
  computation, which can then be referred to in assertion pragmas like loop
  invariants.
* `Ghost types` are those types only useful for defining ghost variables.
* `Ghost procedures` can be used to factor out common treatments on ghost
  variables. Ghost procedures should not have non-ghost outputs, either output
  parameters or global outputs.
* `Ghost packages` provide a means to encapsulate all types and operations for
  a specific kind of ghost code.
* `Imported ghost subprograms` are used to provide placeholders for properties
  that are defined in a logical language, when using manual proof.

When the program is compiled with assertions (for example with switch
``-gnata`` in |GNAT Pro|), ghost code is executed like normal code. Ghost code
can also be selectively enabled by setting pragma ``Assertion_Policy`` as
follows:

.. code-block:: ada

   pragma Assertion_Policy (Ghost => Check);

|GNATprove| checks that ghost code cannot have an effect on the behavior of the
program. |GNAT Pro| compiler also performs some of these checks, although not
all of them. Apart from these checks, |GNATprove| treats ghost code like normal
code during its analyses.

.. _Ghost Functions:

Ghost Functions
^^^^^^^^^^^^^^^

Ghost functions are useful to express properties only used in contracts, and to
factor out common expressions used in contracts. For example, function
``Get_Total`` introduced in :ref:`State Abstraction and Functional Contracts`
to retrieve the value of variable ``Total`` in the contract of ``Add_To_Total``
could be marked as a ghost function as follows:

.. code-block:: ada

   function Get_Total return Integer with Ghost;

and still be used exactly as seen in :ref:`State Abstraction and Functional
Contracts`:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) with
     Pre  => Incr >= 0 and then Get_Total in 0 .. Integer'Last - Incr,
     Post => Get_Total = Get_Total'Old + Incr;

The definition of ``Get_Total`` would be also the same:

.. code-block:: ada

   Total : Integer;

   function Get_Total return Integer is (Total);

Although it is more common to define ghost functions as :ref:`Expression
Functions`, a regular function might be used too:

.. code-block:: ada

   function Get_Total return Integer is
   begin
      return Total;
   end Get_Total;

In that case, |GNATprove| uses only the contract of ``Get_Total`` (either
user-specified or the default one) when analyzing its callers, like for a
non-ghost regular function. (The same exception applies as for regular
functions, when |GNATprove| can analyze a subprogram in the context of its
callers, as described in :ref:`Contextual Analysis of Subprograms Without
Contracts`.)

All functions which are only used in specification can be marked as ghost, but
most don't need to. However, there are cases where marking a specification-only
function as ghost really brings something. First, as ghost entities are not
allowed to interfere with normal code, marking a function as ghost avoids having
to break state abstraction for the purpose of specification. For example,
marking ``Get_Total`` as ghost will prevent users of the package ``Account``
from accessing the value of ``Total`` from non-ghost code.

Then, in the usual context where ghost code is not kept in the final executable,
the user is given more freedom to use in ghost code constructs that are less
efficient than in normal code, which may be useful to express rich
properties. For example, the ghost functions defined in the :ref:`Formal
Containers Library` in |GNAT Pro| typically copy the entire content of the
argument container, which would not be acceptable for non-ghost functions.

.. _Ghost Variables:

Ghost Variables
^^^^^^^^^^^^^^^

Ghost variables are useful to keep track of local or global information during
the computation, which can then be referred to in contracts or assertion
pragmas.

Case 1: Keeping Intermediate Values
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Local ghost variables are commonly used to keep intermediate values. For
example, we can define a local ghost variable ``Init_Total`` to hold the
initial value of variable ``Total`` in procedure ``Add_To_Total``, which allows
checking the relation between the initial and final values of ``Total`` in an
assertion:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) is
      Init_Total : Integer := Total with Ghost;
   begin
      Total := Total + Incr;
      pragma Assert (Total = Init_Total + Incr);
   end Add_To_Total;

Case 2: Keeping Memory of Previous State
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Global ghost variables are commonly used to memorize the value of a previous
state. For example, we can define a global ghost variable ``Last_Incr`` to hold
the previous value passed in argument when calling procedure ``Add_To_Total``,
which allows checking in its precondition that the sequence of values passed in
argument is non-decreasing:

.. code-block:: ada

   Last_Incr : Integer := Integer'First with Ghost;

   procedure Add_To_Total (Incr : in Integer) with
     Pre => Incr >= Last_Incr;

   procedure Add_To_Total (Incr : in Integer) is
   begin
      Total := Total + Incr;
      Last_Incr := Incr;
   end Add_To_Total;

Case 3: Logging Previous Events
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Going beyond the previous case, global ghost variables can be used to store a
complete log of events. For example, we can define global ghost variables
``Log`` and ``Log_Size`` to hold the sequence of values passed in argument to
procedure ``Add_To_Total``, as in :ref:`State Abstraction`:

.. code-block:: ada

   Log      : Integer_Array with Ghost;
   Log_Size : Natural with Ghost;

   procedure Add_To_Total (Incr : in Integer) with
     Post => Log_Size = Log_Size'Old + 1 and Log = Log'Old'Update (Log_Size => Incr);

   procedure Add_To_Total (Incr : in Integer) is
   begin
      Total := Total + Incr;
      Log_Size := Log_Size + 1;
      Log (Log_Size) := Incr;
   end Add_To_Total;

The postcondition of ``Add_To_Total`` above expresses that ``Log_Size`` is
incremented by one at each call, and that the current value of parameter
``Incr`` is appended to ``Log`` at each call (using :ref:`Attribute Old` and
:ref:`Attribute Update`).

Case 4: Expressing Existentially Quantified Properties
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In |SPARK|, universal quantification is only allowed in restricted cases
(over integer ranges and over the content of a container). To express the
existence of a particular object, it is sometimes easier to simply provide it.
This can be done using a global ghost variable. This can be used in particular
to split the specification of a complex procedure into smaller parts:

.. code-block:: ada
        
   X_Interm : T with Ghost;

   procedure Do_Two_Thing (X : in out T) with
     Post => First_Thing_Done (X'Old, X_Interm) and then
             Second_Thing_Done (X_Interm, X)
   is
     X_Init : constant T := X with Ghost;
   begin
     Do_Something (X);
     pragma Assert (First_Thing_Done (X_Init, X));
     X_Interm := X;
 
     Do_Something_Else (X);
     pragma Assert (Second_Thing_Done (X_Interm, X));
   end Do_Two_Things;

More complicated uses can also be envisioned, up to constructing ghost data
structures reflecting complex properties. For example, we can express that two
arrays are a permutation of each other by constructing a permutation from one
to the other:

.. code-block:: ada

  Perm : Permutation with Ghost;
 
  procedure Permutation_Sort (A : Nat_Array) with
    Post => A = Apply_Perm (Perm, A'Old)
  is
  begin
    --  Initalize Perm with the identity
    Perm := Identity_Perm;
    
    for Current in A'First .. A'Last - 1 loop
      Smallest := Index_Of_Minimum_Value (A, Current, A'Last);
      if Smallest /= Current then
        Swap (A, Current, Smallest);
    
        --  Update Perm each time we permute two elements in A
        Permute (Perm, Current, Smallest);
      end if;
     end loop;
   end Permutation_Sort;

.. _Ghost Types:

Ghost Types
^^^^^^^^^^^

Ghost types can only be used to define ghost variables. For example, we can
define ghost types ``Log_Type`` and ``Log_Size_Type`` that specialize the types
``Integer_Array`` and ``Natural`` for ghost variables:

.. code-block:: ada

   subtype Log_Type is Integer_Array with Ghost;
   subtype Log_Size_Type is Natural with Ghost;

   Log      : Log_Type with Ghost;
   Log_Size : Log_Size_Type with Ghost;

Ghost Procedures
^^^^^^^^^^^^^^^^

Ghost procedures are useful to factor out common treatments on ghost
variables. For example, we can define a ghost procedure ``Append_To_Log`` to
append a value to the log as seen previously.

.. code-block:: ada

   Log      : Integer_Array with Ghost;
   Log_Size : Natural with Ghost;

   procedure Append_To_Log (Incr : in Integer) with
     Ghost,
     Post => Log_Size = Log_Size'Old + 1 and Log = Log'Old'Update (Log_Size => Incr);

   procedure Append_To_Log (Incr : in Integer) is
   begin
      Log_Size := Log_Size + 1;
      Log (Log_Size) := Incr;
   end Append_To_Log;

Then, this procedure can be called in ``Add_To_Total`` as follows:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) is
   begin
      Total := Total + Incr;
      Append_To_Log (Incr);
   end Add_To_Total;

.. _Ghost Packages:

Ghost Packages
^^^^^^^^^^^^^^

Ghost packages are useful to encapsulate all types and operations for a
specific kind of ghost code. For example, we can define a ghost package
``Logging`` to deal with all logging operations on package ``Account``:

.. code-block:: ada

   package Logging with
     Ghost
   is
      Log      : Integer_Array;
      Log_Size : Natural;

      procedure Append_To_Log (Incr : in Integer) with
        Post => Log_Size = Log_Size'Old + 1 and Log = Log'Old'Update (Log_Size => Incr);

      ...

   end Logging;

The implementation of package ``Logging`` is the same as if it was not a ghost
package. In particular, a ``Ghost`` aspect is implicitly added to all
declarations in ``Logging``, so it is not necessary to specify it explicitly.
``Logging`` can be defined either as a local ghost package or as a separate
unit. In the latter case, unit ``Account`` needs to reference unit ``Logging``
in a with-clause like for a non-ghost unit:

.. code-block:: ada

   with Logging;

   package Account is
      ...
   end Account;

Imported Ghost Subprograms
^^^^^^^^^^^^^^^^^^^^^^^^^^

When using manual proof (see :ref:`GNATprove and Manual Proof`), it may be more
convenient to define some properties in the logical language of the prover
rather than in |SPARK|. In that case, ghost functions might be marked as
imported, so that no implementation is needed. For example, the ghost procedure
``Append_To_Log`` seen previously may be defined equivalently as a ghost
imported function as follows:

.. code-block:: ada

   function Append_To_Log (Log : Log_type; Incr : in Integer) return Log_Type with
     Ghost,
     Import;

where ``Log_Type`` is an Ada type used also as placeholder for a type in the
logical language of the prover. To avoid any inconsistency between the
interpretations of ``Log_Type`` in |GNATprove| and in the manual prover, it is
preferable in such a case to mark the definition of ``Log_Type`` as not in
|SPARK|, so that |GNATprove| does not make any assumptions on its content. This
can be achieved by defining ``Log_Type`` as a private type and marking the
private part of the enclosing package as not in |SPARK|:

.. code-block:: ada

   package Logging with
     SPARK_Mode,
     Ghost
   is
      type Log_Type is private;

      function Append_To_Log (Log : Log_type; Incr : in Integer) return Log_Type with
        Import;

      ...

   private
      pragma SPARK_Mode (Off);

      type Log_Type is new Integer;  --  Any definition is fine here
   end Logging;

A ghost imported subprogram cannot be executed, so calls to ``Append_To_Log``
above should not be enabled during compilation, otherwise a compilation error
is issued. Note also that |GNATprove| will not attempt proving the contract of
a ghost imported subprogram, as it does not have its body.

.. _Ghost Models:

Ghost Models
^^^^^^^^^^^^
When specifying a program, it is common to use a model, that is, an alternative,
simpler view of a part of the program. As they are only used in annotations,
models can be computed using ghost code.

Models of Control Flow
~~~~~~~~~~~~~~~~~~~~~~

Global variables can be used to enforce properties over call cahains in the
program. For example, we may want to express that ``Total`` cannot be
incremented twice in a row without registering the transaction in between. This
can be done by introducing a ghost global variable
``Last_Transaction_Registered``, used to encode whether ``Register_Transaction``
was called since the last call to ``Add_To_Total``:

.. code-block:: ada

  Last_Transaction_Registered : Boolean := True with Ghost;

  procedure Add_To_Total (Incr : Integer) with
    Pre  => Last_Transaction_Registered,
    Post => not Last_Transaction_Registered;

  procedure Register_Transaction with
    Post => Last_Transaction_Registered;

The value of Last_Transaction_Registered should also be updated in the body of
``Add_To_Total`` and ``Register_Transaction`` to reflect their contracts:

.. code-block:: ada

   procedure Add_To_Total (Incr : in Integer) is
   begin
      Total := Total + Incr;
      Last_Transaction_Registered := False;
   end Add_To_Total;

More generally, the expected control flow of a program can be modeled using an
automaton. We can take as an example a mailbox containing only one message.
The expected way ``Receive`` and ``Send`` should be interleaved can be expressed
as a two state automaton. The mailbox can either be full, in which case
``Receive`` can be called but not ``Send``, or it can be empty, in which case it
is ``Send`` that can be called and not ``Receive``. To express this property, we
can define a ghost global variable of a ghost enumeration type to hold the
state of the automaton:
    
.. code-block:: ada

   type Mailbox_Status_Kind is (Empty, Full) with Ghost;
   Mailbox_Status : Mailbox_Status_Kind := Empty with Ghost;

   procedure Receive (X : out Message) with
     Pre  => Mailbox_Status = Full,
     Post => Mailbox_Status = Empty;
     
   procedure Send (X : Message) with
     Pre  => Mailbox_Status = Empty,
     Post => Mailbox_Status = Full;

Like before, ``Receive`` and ``Send`` should update ``Mailbox_Status`` in their
bodies.
Note that all the transitions of the automaton need not be specified, only the
part which are relevant to the properties we want to express.

If the program also has some regular state, an invariant can be used to link
the value of this state to the value of the ghost state of the automaton. For
example, in our mailbox, we may have a regular variable ``Message_Content``
holding the content of the current message, which is only known to be valid
after a call to ``Send``. We can introduce a ghost function linking the value
of ``Message_Content`` to the value of ``Mailbox_Status``, so that we can
ensure that ``Message_Content`` is always valid when accessed from ``Receive``:

.. code-block:: ada

  function Invariant return Boolean is
    (if Mailbox_Status = Full then Valid (Message_Content))
  with Ghost;

  procedure Receive (X : out Message) with
    Pre  => Invariant and then Mailbox_Status = Full,
    Post => Invariant and then Mailbox_Status = Empty
        and then Valid (X)
  is
    X := Message_Content;
  end Receive;

Models of Data Structures
~~~~~~~~~~~~~~~~~~~~~~~~~

For specifying programs that use complex data structures (doubly-linked lists,
maps...), it can be useful to supply a model for the data structure. A model
is an alternative, simpler view of the data-structure which allows to write
properties more easily. For example, a ring buffer, or a doubly-linked list, can
be modeled using an array containing the elements from the buffer or the list in
the right order. Typically, though simpler to reason with, the model is less
efficient than the regular data structure. For example, inserting an element at
the beginning of a doubly-linked list or at the beginning of a ring buffer can
be done in constant time whereas inserting an element at the beginning of an
array requires to slide all the elements to the right. As a result, models of
data structures are usually supplied using ghost code. As an example, the
package ``Ring_Buffer`` offers an implementation of a single instance ring
buffer. A ghost variable ``Buffer_Model`` is used to write the specification of
the ``Enqueue`` procedure:

.. code-block:: ada
		
  package Ring_Buffer is
    function Get_Model return Nat_Array with Ghost;
    
    procedure Enqueue (E : Natural) with
      Post => Get_Model = E & Get_Model'Old (1 .. Max – 1);
  private
    Buffer_Content : Nat_Array;
    Buffer_Top     : Natural;
    Buffer_Model   : Nat_Array with Ghost;
    
    function Get_Model return Nat_Array is (Buffer_Model);
  end Ring_Buffer;

Then, just like for models of control flow, an invariant should be supplied to
link the regular data structure to its model:

.. code-block:: ada
		
  package Ring_Buffer is
    function Get_Model return Nat_Array with Ghost;
    function Invariant return Boolean with Ghost;
    
    procedure Enqueue (E : Natural) with
      Pre  => Invariant,
      Post => Invariant and then Get_Model = E & Get_Model'Old (1 .. Max – 1);
  private
    Buffer_Content : Nat_Array;
    Buffer_Top     : Natural;
    Buffer_Model   : Nat_Array with Ghost;
    
    function Get_Model return Nat_Array is (Buffer_Model);
    function Invariant return Boolean is
      (Buffer_Model = Buffer_Content (Buffer_Top .. Max)
                    & Buffer_Content (1 .. Buffer_Top - 1));
  end Ring_Buffer;

If a data structure type is defined, a ghost function can be provided to
compute a model for objects of the data structure type, and the invariant can
be stated as a postcondition of this function:

.. code-block:: ada
		
  package Ring_Buffer is
    type Buffer_Type is private;
    subtype Model_Type is Nat_Array with Ghost;
    
    function Invariant (X : Buffer_Type; M : Model_Type) return Boolean with
      Ghost;
    function Get_Model (X : Buffer_Type) return Model_Type with
      Ghost,
      Post => Invariant (X, Get_Model'Result);
    
    procedure Enqueue (X : in out Buffer_Type; E : Natural) with
      Post => Get_Model (X) = E & Get_Model (X)'Old (1 .. Max – 1);
  private
    type Buffer_Type is record
      Content : Nat_Array;
      Top     : Natural;
    end record;
  end Ring_Buffer;

More complex examples of models of data structure can be found in the
:ref:`Formal Containers Library`.
  
.. _Removal of Ghost Code:

Removal of Ghost Code
^^^^^^^^^^^^^^^^^^^^^

By default, |GNAT Pro| completely discards ghost code during compilation, so
that no ghost code is present in the object code or the executable. This
ensures that, even if parts of the ghost could have side-effects when executed
(writing to variables, performing system calls, raising exceptions, etc.), by
default the compiler ensures that it cannot have any effect on the behavior of
the program.

This is also essential in domains submitted to certification where all
instructions in the object code should be traceable to source code and
requirements, and where testing should ensure coverage of the object code. As
ghost code is not present in the object code, there is no additional cost for
maintaining its traceability and ensuring its coverage by tests.

|GNAT Pro| provides an easy means to check that no ignored ghost code is
present in a given object code or executable, which relies on the property
that, by definition, each ghost declaration or ghost statement mentions at
least one ghost entity. |GNAT Pro| prefixes all names of such ignored ghost
entities in the object code with the string ``___ghost_`` (except for names of
ghost compilation units). The initial triple underscore ensures that this
substring cannot appear anywhere in the name of non-ghost entities or ghost
entities that are not ignored. Thus, one only needs to check that the substring
``___ghost_`` does not appear in the list of names from the object code or
executable.

On Unix-like platforms, this can done by checking that the following command
does not output anything::

  nm <object files or executable> | grep ___ghost_

The same can be done to check that a ghost compilation unit called ``my_unit``
(whatever the capitalization) is not included at all (entities in that unit
would have been detected by the previous check) in the object code or
executable. For example on Unix-like platforms:

  nm <object files or executable> | grep my_unit
