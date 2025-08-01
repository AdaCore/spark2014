Specification Features
======================

|SPARK| contains many features for specifying the intended behavior of
programs. Some of these features come from Ada 2012 (:ref:`Attribute Old` and
:ref:`Expression Functions` for example). Other features are specific to
|SPARK| (:ref:`Attribute loop_Entry` and :ref:`Ghost Code` for example). In
this section, we describe these features and their impact on execution and
formal verification.

.. index:: Constant_After_Elaboration

.. _Aspect Constant_After_Elaboration:

Aspect ``Constant_After_Elaboration``
-------------------------------------

*Specific to SPARK*

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

.. index:: No_Caching

Aspect ``No_Caching``
---------------------

*Specific to SPARK*

Aspect ``No_Caching`` can be specified for a volatile type or a volatile
variable to indicate that this type or variable can be analyzed as non-volatile
by |GNATprove|. This is typically used to hold the value of local variables
guarding the access to some critical section of the code. To defend against
fault injection attacks, a common practice is to duplicate the test guarding
the critical section, and the variable is marked as volatile to prevent the
compiler from optimizing out the duplicate tests. For example:

.. code-block:: ada

    Cond : Boolean with Volatile, No_Caching := Some_Computation;

    if not Cond then
        return;
    end if;

    if not Cond then
        return;
    end if;

    if Cond then
        -- here do some critical work
    end if;

Without ``No_Caching``, the volatile variable is assumed to be used for
:ref:`Interfaces to the Physical World`, |GNATprove| analyses it specially and
one cannot declare it inside a subprogram.

.. _Aspect Relaxed_Initialization:

Aspect ``Relaxed_Initialization`` and Ghost Attribute ``Initialized``
---------------------------------------------------------------------

*Specific to SPARK*

Modes on parameters and data dependency contracts in |SPARK| have a stricter
meaning than in Ada (see :ref:`Data Initialization Policy`). In general, this
allows |GNATprove| to ensure correct initialization of data in a quick and
scalable way through flow analysis, without the need for user-supplied
annotations.
However, in some cases, the initialization policy may be considered too
constraining. In particular, it does not permit initializing composite objects
by part through different subprograms, or leaving data uninitialized on return
if an error occurred.

.. index:: Relaxed_Initialization

Aspect ``Relaxed_Initialization``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

To handle these cases, it is possible to relax the standard data initialization
policy of |SPARK| using the ``Relaxed_Initialization`` aspect. This aspect can
be used:

* on objects, to state that the object should not be subject to the
  initialization policy of |SPARK|,

* on types, so that it applies to every object or component of the type, or

* on subprograms, to annotate the parameters or result.

Here are some examples:

.. code-block:: ada

   type My_Rec is record
      F, G : Positive;
   end record;

   G : My_Rec with Relaxed_Initialization;
   procedure Init_G_If_No_Errors (Error : out Boolean) with
      Global => (Output => G);
   --  G is only initialized if the Error flag is False

In the snippet above, the aspect ``Relaxed_Initialization`` is used to annotate
the object ``G`` so that |SPARK| will allow returning from
``Init_G_If_No_Errors`` with an uninitialized value in ``G`` in case of errors
in the initialization routine.

On a subprogram, the ``Relaxed_Initialization`` aspect expects some parameters
to specify to which objects it applies. For example, the parameter ``X`` of
the procedures below is concerned by the aspect:

.. code-block:: ada

   procedure Init_Only_F (X : out My_Rec) with
     Relaxed_Initialization => X;
   --  Initialize the F component of X,
   --  X.G should not be read after the call.

   procedure Init_Only_G (X : in out My_Rec) with
     Relaxed_Initialization => X;
   --  Initialize the G component of X,
   --  X.F can be read after the call if it was already initialized.

The procedures ``Init_Only_F`` and ``Init_Only_G`` above differ only by the
mode of parameter ``X``. Just like for ``Init_G_If_No_Errors``, the
mode ``out`` in ``Init_Only_F`` does not mean that ``X`` should be
entirely initialized by the call. Its purpose is mostly for data dependencies
(see :ref:`Data Dependencies`). It states that the value on entry of the
procedure call should not leak into the parts of the output value which are
read after the call. To ensure that, |GNATprove| considers that ``out``
parameters may not be copied when entering a procedure call, and so, even for
parameters which are in fact passed by reference.

To exempt the value returned by a function from the data initialization policy
of |SPARK|, the result attribute can be specified as a parameter of the
``Relaxed_Initialization`` aspect, as in ``Read_G`` below. It is also
possible to give several objects to the aspect using an aggregate notation:

.. code-block:: ada

   procedure Copy (Source : My_Rec; Target : out My_Rec) with
     Relaxed_Initialization => (Source, Target);
   --  Can copy a partially initialized record

   function Read_G return My_Rec with
     Relaxed_Initialization => Read_G'Result;
   --  The result of Read_G might not be initialized

.. note::

   The ``Relaxed_Initialization`` aspect has no effect on subprogram parameters
   or function results of a scalar type with relaxed initialization. Indeed,
   the Ada semantics mandates a copy of scalars on entry and return of
   subprograms, which is considered to be an error if the object was not
   initialized.

Finally, if we want to exempt all objects of a type from the data
initialization policy of |SPARK|, it is possible to specify the
``Relaxed_Initialization`` aspect on a type. This also allows to exempt a
single component of a record, like in the following example:

.. code-block:: ada

   type Content_Type is array (Positive range 1 .. 100) of Integer with
     Relaxed_Initialization;
   type Stack is record
      Top     : Natural := 0;
      Content : Content_Type;
   end record
     with Predicate => Top in 0 .. 100;
   --  Elements located after Top in Content do not need to be initialized

A stack is made of two components: an array ``Content`` storing the actual
content of the stack, and the index ``Top`` of the topmost element currently
allocated on the stack. If the stack is initialized, the ``Top`` component
necessarily holds a meaningful value. However, because of the API of the stack,
it is not possible to read a value stored above the ``Top`` index in
``Content`` without writing it first. For this reason, it is not necessary to
initialize all elements of the stack at creation. To express that, we use in
the type ``Stack``, which itself is subject to the standard initialization
policy, an array with the ``Relaxed_Initialization`` aspect for the ``Content``
field.

.. note::

  The ``Relaxed_Initialization`` aspect is not allowed on subtypes, so a
  derived type is necessary to add the aspect to an existing type.

.. index:: Initialized

Ghost Attribute ``Initialized``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

As explained above, the standard data initialization policy does not apply to
objects annotated with the ``Relaxed_Initialization`` aspect. As a result, it
becomes necessary to annotate which parts of accessed objects are initialized on
entry and exit of subprograms in contracts. This can be done using the
``Initialized`` ghost attribute. This attribute can be applied to (parts of)
objects annotated with the ``Relaxed_Initialization`` aspect. If the object is
completely initialized, except possibly for subcomponents of the object whose
type is annotated with the ``Relaxed_Initialization`` aspect, this attribute
evaluates to ``True``.

.. note::

  It is not true that the ``Initialized`` aspect necessarily evaluates to
  ``False`` on uninitialized data. This is to comply with execution, where
  some values may happen to be valid even if they have not been initialized.
  However, it is not possible to prove that the ``Initialized`` aspect
  evaluates to ``True`` if the object has not been entirely initialized.

As an example, let's add some contracts to the subprograms presented in the
previous example to replace the comments. The case of ``Init_G_If_No_Errors``
is straightforward:

.. code-block:: ada

   procedure Init_G_If_No_Errors (Error : out Boolean) with
     Post => (if not Error then G'Initialized);

It states that if no errors have occurred (``Error`` is ``False`` on exit),
``G`` has been initialized by the call.

The postcondition of ``Read_G`` is a
bit more complicated. We want to state that the function returns the value
stored in ``G``. However, we cannot use equality, as it would evaluate the
components of both operands and fail if ``G`` is not entirely initialized. What
we really want to say is that each component of the result of ``Read_G`` will
be initialized if and only if the corresponding component in ``G`` is
initialized, and then that the values of the components necessarily match in
this case. To
express that, we introduce safe accessors for the record components, which
check whether the field is initialized before returning it. If the component
is not initialized, they return ``0`` which is an invalid value since both
components of ``My_Rec`` are of type ``Positive``. This allows to encode both
the initialization status and the value of the field in one go:

.. code-block:: ada

   function Get_F (X : My_Rec) return Integer is
      (if X.F'Initialized then X.F else 0)
   with Ghost,
     Relaxed_Initialization => X;

   function Get_G (X : My_Rec) return Integer is
      (if X.G'Initialized then X.G else 0)
   with Ghost,
     Relaxed_Initialization => X;

Using these accessors, we can define an equality which can safely be called on
uninitialized data, and use it in the postcondition of ``Read_G``:

.. code-block:: ada

   function Safe_Eq (X, Y : My_Rec) return Boolean is
     (Get_F (X) = Get_F (Y) and Get_G (X) = Get_G (Y))
   with Ghost,
     Relaxed_Initialization => (X, Y);

   function Read_G return My_Rec with
     Relaxed_Initialization => Read_G'Result,
     Post => Safe_Eq (Read_G'Result, G);

The same safe equality function can be used for the postcondition of ``Copy``:

.. code-block:: ada

   procedure Copy (Source : My_Rec; Target : out My_Rec) with
     Relaxed_Initialization => (Source, Target),
     Post => Safe_Eq (Source, Target);

Remain the procedures ``Init_Only_F`` and ``Init_Only_G``. We reflect the
asymmetry of their parameter modes in their postconditions:

.. code-block:: ada

   procedure Init_Only_F (X : out My_Rec) with
     Relaxed_Initialization => X,
     Post => X.F'Initialized;

   procedure Init_Only_G (X : in out My_Rec) with
     Relaxed_Initialization => X,
     Post => X.G'Initialized and Get_F (X) = Get_F (X)'Old;

The procedure ``Init_Only_G`` preserves the value of ``X.F`` whereas
``Init_Only_F`` does not preserve ``X.G``. Note that a postcondition similar
to the one of ``Init_Only_G`` would be proved on ``Init_Only_F``, but it will be
of no use as ``out`` parameters are considered to be havocked at the beginning
of procedure calls, so ``Get_G (X)'Old`` wouldn't actually refer to the value
of ``G`` before the call.

Finally, let's consider the type ``Stack`` defined above. We have annotated
the array type used for its content with the ``Relaxed_Initialization`` aspect,
so that we do not need to initialize all of its components at declaration.
However, we still need to know that elements up to ``Top`` have been
initialized to ensure that poping an element returns an initialized value.
This can be stated by extending the subtype predicate of ``Stack`` in the
following way:

.. code-block:: ada

   type Stack is record
      Top     : Natural := 0;
      Content : Content_Type;
   end record
     with Ghost_Predicate => Top in 0 .. 100
       and then (for all I in 1 .. Top => Content (I)'Initialized);

Since ``Content_Type`` is annotated with the ``Relaxed_Initialization`` aspect,
references to the attribute ``Initialized`` on an object of type ``Stack`` will
not consider the elements of ``Content``, so ``S'Initialized`` can evaluate to
True even if the stack ``S`` contains uninitialized elements.

.. note::

   The predicate of type ``Stack`` is now introduced by aspect
   ``Ghost_Predicate`` to allow the use of ghost attribute ``Initialized``.

.. note::

  When the ``Relaxed_Initialization`` aspect is used, correct initialization is verified by proof (``--mode=all`` or ``--mode=silver``), and not flow analysis (``--mode=flow`` or ``--mode=bronze``).

  It is possible to annotate an object with the ``Relaxed_Initialization``
  aspect to use proof to verify its initialization. For example, it allows to
  workaround limitations in flow analysis with respect to initialization
  of arrays. However, if this initialization goes through a loop, using the
  ``Initialized`` attribute in a loop invariant might be required for proof to
  verify the program.

.. index:: Side_Effects
           side effects; in functions

.. _Aspect Side_Effects:

Aspect ``Side_Effects``
-----------------------

*Specific to SPARK*

Unless stated otherwise, functions in |SPARK| cannot have side effects:

- A function must not have an ``out`` or ``in out`` parameter.

- A function must not write a global variable.

- A function must not raise exceptions.

- A function must always terminate.

The aspect ``Side_Effects`` can be used to indicate that a function may in fact
have side effects, among the four possible side effects listed above. A
`function with side effects` can be called only as the right-hand side of an
assignment, as part of a list of statements where a procedure could be called:

.. code-block:: ada

   function Increment_And_Return (X : in out Integer) return Integer
     with Side_Effects;

   procedure Call is
     X : Integer := 5;
     Y : Integer;
   begin
     Y := Increment_And_Return (X);
     --  The value of X is 6 here
   end Call;

Note that a function with side effects could in general be converted into a
procedure with an additional ``out`` parameter for the function's
result. However, it can be more convenient to use a function with side effects
when binding SPARK code with C code where functions have very often
side effects.

.. index:: Potentially_Invalid

.. _Aspect Potentially_Invalid:

Aspect ``Potentially_Invalid``
------------------------------

*Specific to SPARK*

In general, |GNATprove| requires all initialized values mentioned in |SPARK|
code to be valid (see :ref:`Data Validity`). This is enforced by the combination
of the initialization policy of |SPARK|, assumptions on data created or modified
by non-|SPARK| code, and specific checks on unchecked conversions and objects
with precisely supported address clauses.

The ``Potentially_Invalid`` aspect can be used to instruct |GNATprove| that
particular objects might have invalid values. It will cause it to generate
validity checks when the object is accessed. More precisely, the
``Potentially_Invalid`` aspect can be specified on standalone objects,
subprogram parameters and function results as follows:

.. code-block:: ada

   type Int_8 is range -128 .. 127 with Size => 8;
   subtype Nat_8 is Int_8 range 0 .. 127;

   type My_Record is record
      F, G, H, I : Nat_8;
   end record;

   G : My_Record with Potentially_Invalid;
   procedure P (X, Y : in out My_Record) with
     Potentially_Invalid => (X, Y);
   function F return My_Record with
     Potentially_Invalid => F'Result;

Potentially invalid objects might be of a scalar type or of a composite type.
However, the potentially invalid annotation on composite objects only applies to
regular record fields or array components. Array bounds and record
discriminants should always be valid even for objects annotated with
``Potentially_Invalid``.

As a general rule, a validity check is emitted each time a potentially invaid
object is evaluated. However, if a composite object is potentially invalid, it
can be copied into another potentially invalid object without trigerring a
validity check. Instead, the validity status is propagated. This can happen
in object declarations, assignments, on function return, on actual
parameters in subprogram calls, and in references to the ``Old`` and
``Loop_Entry`` attributes.
As an example, no validity checks are emitted on the following code snippet. The
validity statuses are propagated through the various copies involved:

.. code-block:: ada

   declare
      C : My_Record := G with Potentially_Invalid;
   begin
      G := F;
      P (C, G);
   end;

Copying an invalid scalar object is a bounded error in Ada. As a result, the
validity status of a scalar object or call is in general not propagated and a
validity check is emitted. As an exception, no validity checks are emitted for
function calls occuring in declarations or assignments into potentially invalid
scalar objects if the function is imported and its return type is the expected
subtype. As an example, no validity check is emitted on the following call:

.. code-block:: ada

   function F_2 return Nat_8 with
     Potentially_Invalid => F_2'Result, Import;

   C_2 : Nat_8 := F_2 with Potentially_Invalid;

It is also possible to annotate an instance of ``Ada.Unchecked_Conversion``
with the ``Potentially_Invalid`` aspect, as examplified below:

.. code-block:: ada

   type Uint_32 is mod 2 ** 32;
   function Unsafe_Read_Record is new Ada.Unchecked_Conversion (Uint_32, My_Record) with
     Potentially_Invalid;

A call to such an instance is considered to return a potentially invalid value,
similarly to what is done for regular functions. It can be used to initialize
composite as well as scalar objects, as long as the target type of the unchecked
conversion and the object type match. Adding such an annotation to an instance
of ``Ada.Unchecked_Conversion`` also causes |GNATprove| not to emit the
checks that are usually generated to ensure that the target type of an unchecked
conversion does not have invalid values. As a result, the example above is
entirely proved even though ``Nat_8`` has invalid values.

References to potentially invalid objects might not trigger validity checks if
the object is not evaluated, or at least, only necessarily valid part of the
object are evaluated. It is the case for the prefix of the ``Valid`` and
``Valid_Scalars`` attributes and access to array bounds and discriminants of
potentially invalid objects in particular. No validity checks are emitted in the
following code as no potentially invalid parts of an object are evaluated:

.. code-block:: ada

   type My_Array is array (1 .. 4) of Nat_8;

   pragma Assert (G'Valid_Scalars and C_Pos'Valid);
   declare
      V : My_Array with Potentially_Invalid;
   begin
      pragma Assert (V'Length = 4);
   end;

All other uses of potentially invalid objects trigger validity checks. A
reference to the ``Valid`` or ``Valid_Scalar`` on a prefix that is not
potentially invalid will result in a warning. The ``Potentially_Invalid_Reads``
procedure is an example of how the feature might be used. The
``Record_Or_Array`` type has a discriminant, it might be either a record or an
array of non-negative integer values. The ``Unsafe_Read`` procedure uses
unchecked conversion instances to initialize an object of this type, potentially
creating invalid values. It reads the discriminant of its parameter. It does not
trigger a validity check as discriminants of potentially invalid objects are
necessarily valid. The ``Safe_Read`` procedure uses the ``Valid_Scalars``
attribute to bail out with an exception if an invalid value is read. The two
procedures ``Use_Safe_Read`` and ``Use_Unsafe_Read`` follow the same pattern.
They first read a value, using either ``Safe_Read`` or ``Unsafe_Read``, and then
apply some treatment on it using ``Treat_Array_Or_Record`` which only expects
valid values, without any additional safe guard:

.. literalinclude:: /examples/ug__potentially_invalid_reads/potentially_invalid_reads.adb
   :language: ada
   :linenos:

Here |GNATprove| detects that an invalid value might be read in
``Use_Unsafe_Read``. The rest of the example is entirely verified:

.. literalinclude:: /examples/ug__potentially_invalid_reads/test.out
   :language: none

.. note::

   Assuming an out-of-bound value for a scalar object might create an
   unsoundness in the logic of |SPARK|, and so, even if the object is annotated
   with ``Potentially_Invalid``. This might result in incorrectly verified
   checks. If the whole program is in |SPARK|, this cannot happen, as
   |GNATprove| emits checks to ensure that potentially invalid values are never
   read. If a program is not entirely written is |SPARK|, care should be taken
   to never introduce such assumptions in code visible by |GNATprove|, in
   particular in postconditions of non-|SPARK| subprograms. To help with this
   review, the |GNATprove| tool emits a warning whenever a potentially
   invalid object is read in the postcondition of a non-|SPARK| subprogram,
   unless it can determine that the access is safe. As an example, |GNATprove|
   will emit a warning on the ``Result`` attribute in the postcondition of
   ``One_Bad`` but not in th  postcondition of ``One_OK`` as it can determine
   that it is safe, due to the short-circuit conjunction with the ``Valid``
   attribute:

   .. literalinclude:: /examples/ug__potentially_invalid_warning/potentially_invalid_warning.adb
      :language: ada
      :linenos:

   .. literalinclude:: /examples/ug__potentially_invalid_warning/test.out
      :language: none

.. index:: Loop_Entry
           loop; and Loop_Entry

.. _Attribute Loop_Entry:

Attribute ``Loop_Entry``
------------------------

*Specific to SPARK*

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

.. index:: Old

.. _Attribute Old:

Attribute ``Old``
-----------------

*Supported in Ada 2012*

.. index:: postcondition; and Old

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


.. index:: Contract_Cases; and Old

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

.. index:: Unevaluated_Use_Of_Old

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

.. index:: Result
           postcondition; and Result
           Contract_Cases; and Result

.. _Attribute Result:

Attribute ``Result``
--------------------

*Supported in Ada 2012*

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

.. index:: aggregate

Aggregates
----------

Aggregates are expressions, and as such can appear in assertions and contracts
to specify the value of a composite type (record or array), without having to
specify the value of each component of the object separately.

Record Aggregates
^^^^^^^^^^^^^^^^^

*Supported in Ada 83*

Since the first version, Ada has a compact syntax for expressing the value of a
record type, optionally allowing to name the components. Given the following
declaration of type ``Point``:

.. code-block:: ada

   type Point is record
      X, Y, Z : Float;
   end record;

the value of the origin can be expressed with a named notation:

.. code-block:: ada

   Origin : constant Point := (X => 0.0, Y => 0.0, Z => 0.0);

or with a positional notation, where the values for components are taken in the
order in which they are declared in type ``Point``, so the following is
equivalent to the above named notation:

.. code-block:: ada

   Origin : constant Point := (0.0, 0.0, 0.0);

With named notation, components can be given in any order:

.. code-block:: ada

   Origin : constant Point := (Z => 0.0, Y => 0.0, X => 0.0);

Positional notation and named notation can be mixed, but, in that case, named
associations should always follow positional associations, so positional
notation will refer to the first components of the record, and named notation
will refer to the last components of the record:

.. code-block:: ada

   Origin : constant Point := (0.0, Y => 0.0, Z => 0.0);
   Origin : constant Point := (0.0, 0.0, Z => 0.0);

Choices can be grouped with the bar symbol ``|`` to denote sets:

.. code-block:: ada

   Origin : constant Point := (X | Y | Z => 0.0);

The choice ``others`` can be used with a value to refer to all other
components, provided these components have the same type, and the ``others``
choice should come last:

.. code-block:: ada

   Origin : constant Point := (X => 0.0, others => 0.0);
   Origin : constant Point := (Z => 0.0, others => 0.0);
   Origin : constant Point := (0.0, others => 0.0);  --  positional for X
   Origin : constant Point := (others => 0.0);

The box notation ``<>`` can be used instead of an explicit value to denote the
default value of the corresponding type:

.. code-block:: ada

   Origin : constant Point := (X => <>, Y => 0.0, Z => <>);

In SPARK, this is only allowed if the types of the corresponding components
have a default value, for example here:

.. code-block:: ada

   type Zero_Init_Float is new Float with Default_Value => 0.0;

   type Point is record
      X : Float := 0.0;
      Y : Float;
      Z : Zero_Init_Float;
   end record;

Note that, when using box notation ``<>`` with an ``others`` choice, it is not
required that these components have the same type.

Array Aggregates
^^^^^^^^^^^^^^^^

*Supported in Ada 83*

Since the first version, Ada has the same compact syntax for expressing the
value of an array type as for record types, optionally allowing to name the
indexes. Given the following declaration of type ``Point``:

.. code-block:: ada

   type Dimension is (X, Y, Z);

   type Point is array (Dimension) of Float;

the value of the origin can be expressed with a named notation:

.. code-block:: ada

   Origin : constant Point := (X => 0.0, Y => 0.0, Z => 0.0);

or with a positional notation, where the values for components are taken in the
order in which they are declared in type ``Point``, so the following is
equivalent to the above named notation:

.. code-block:: ada

   Origin : constant Point := (0.0, 0.0, 0.0);

With the difference that named notation and positional notation cannot be mixed
in an array aggregate, all other explanations presented for aggregates of
record type ``Point`` in :ref:`Record Aggregates` are applicable to array
aggregates here, so all the following declarations are valid:

.. code-block:: ada

   Origin : constant Point := (Z => 0.0, Y => 0.0, X => 0.0);
   Origin : constant Point := (X | Y | Z => 0.0);
   Origin : constant Point := (X => 0.0, others => 0.0);
   Origin : constant Point := (Z => 0.0, others => 0.0);
   Origin : constant Point := (0.0, others => 0.0);  --  positional for X
   Origin : constant Point := (others => 0.0);

while the use of box notation ``<>`` is only allowed in SPARK if array
components have a default value, either through their type, or through aspect
``Default_Component_Value`` on the array type:

.. code-block:: ada

   type Point is array (Dimension) of Float
     with Default_Component_Value => 0.0;

Note that in many cases, indexes take an integer value rather than an
enumeration value:

.. code-block:: ada

   type Dimension is range 1 .. 3;

   type Point is array (Dimension) of Float;

In that case, choices will take an integer value too:

.. code-block:: ada

   Origin : constant Point := (3 => 0.0, 2 => 0.0, 1 => 0.0);
   Origin : constant Point := (1 | 2 | 3 => 0.0);
   Origin : constant Point := (1 => 0.0, others => 0.0);
   Origin : constant Point := (3 => 0.0, others => 0.0);
   Origin : constant Point := (0.0, others => 0.0);  --  positional for 1
   Origin : constant Point := (others => 0.0);

Note that one can also use X, Y and Z in place of literals 1, 2 and 3 with the
prior definition of suitable named numbers:

.. code-block:: ada

   X : constant := 1;
   Y : constant := 2;
   Z : constant := 3;

Note that allocators are allowed inside expressions, and that values in
aggregates are evaluated for each corresponding choice, so it is possible to
write the following without violating the :ref:`Memory Ownership Policy` of
SPARK:

.. code-block:: ada

   type Ptr is access Integer;
   type Data is array (1 .. 10) of Ptr;

   Database : Data := (others => new Integer'(0));

This would be also possible in a record aggregate, but it is more common in
array aggregates.

Iterated Component Associations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

*Supported in Ada 2022*

It is possible to have the value of an association depending on the choice,
with the feature called `iterated component associations`. Here is how we can
express that ``Ident`` is the identity mapping from values in ``Index`` to
themselves:

.. code-block:: ada

   type Index is range 1 .. 100;
   type Mapping is array (Index) of Index;

   Ident : constant Mapping := (for J in Index => J);

Such an iterated component association can appear next to other associations in
an array aggregate using named notation. Here is how we can express that
``Saturation`` is the identity mapping between 10 and 90, and saturates outside
of this range:

.. code-block:: ada

   Saturation : constant Mapping :=
     (1 .. 10 => 10, for J in 11 .. 89 => J, 90 .. 100 => 90);

.. index:: initialization (arrays)

Initialization Using Array Aggregates
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

*Supported in Ada 83*

Both flow analysis and proof can be used in GNATprove to verify that data is
correctly initialized before being read, following the :ref:`Data
Initialization Policy` of SPARK. The decision to use one or the other is based
on the presence or not of aspect ``Relaxed_Initialization`` (see :ref:`Aspect
Relaxed_Initialization`) on types and variables.

When using flow analysis to analyze the initialization of an array object
(variable or component), false alarms may be emitted by |GNATprove| on code
that initializes the array cell by cell, or groups of cells by groups of cells,
even if the array ends up completely initialized. This is because flow analysis
is not value dependent, so it cannot track the value of assigned array indexes.
As a result, it cannot separate array cells in its analysis, hence it cannot
deduce that such a sequence of partial initializations result in the array
being completely initialized. For example, |GNATprove| issues false alarms on
the code:

.. code-block:: ada

   type Arr is array (1 .. 5) of Integer;
   A : Arr;
   ...
   A(1) := 1;
   A(2) := 2;
   A(3) := 3;
   A(4) := 4;
   A(5) := 5;

A better way to initialize an array is to use an aggregate (possibly with
iterated component associations, if the value of the initialization element for
a cell depends on the index of the cell). This makes it clear for both the
human reviewer and for |GNATprove| that the array is completely
initialized. For example, the code above can be rewritten as follows using an
aggregate:

.. code-block:: ada

   type Arr is array (1 .. 5) of Integer;
   A : Arr;
   ...
   A := (1, 2, 3, 4, 5);

or using an aggregate with an iterated component association:

.. code-block:: ada

   type Arr is array (1 .. 5) of Integer;
   A : Arr;
   ...
   A := (for I in 1..5 => I);

In cases where initializing the array with an aggregate is not possible, the
alternative is to mark the array object or its type as having relaxed
initialization using aspect ``Relaxed_Initialization`` and to use proof to
verify its correct initialization (see :ref:`Aspect Relaxed_Initialization`).
This should be reserved for cases where using an aggregate is not possible, as
it requires more work for the user to express which parts of variables are
initialized (in contracts and loop invariants typically), and it may be more
difficult to prove.

.. index:: delta aggregate

Delta Aggregates
^^^^^^^^^^^^^^^^

*Supported in Ada 2022*

It is quite common in :ref:`Postconditions` to relate the input and output
values of parameters. While this can be as easy as ``X = X'Old + 1`` in the
case of scalar parameters, it is more complex to express for array and record
parameters. Delta aggregates are useful in that case, to denote the updated
value of a composite variable. For example, we can express more clearly that
procedure ``Zero_Range`` zeroes out the elements of its array parameter ``X``
between ``From`` and ``To`` by using a delta aggregate:

.. code-block:: ada

   procedure Zero_Range (X : in out Integer_Array; From, To : Positive) with
     Post => X = (X'Old with delta From .. To => 0);

than with an equivalent postcondition using :ref:`Quantified Expressions` and
:ref:`Conditional Expressions`:

.. code-block:: ada

   procedure Zero_Range (X : in out Integer_Array; From, To : Positive) with
     Post => (for all J in X'Range =>
                (if J in From .. To then X(J) = 0 else X(J) = X'Old(J)));

Delta aggregates allow to specify a list of associations between indexes
(for arrays) or components (for records) and values. Components can only be
mentioned once, with the semantics that all values are evaluated before any
update. Array indexes may be mentioned more than once, with the semantics that
updates are applied in left-to-right order. For example, the postcondition of
procedure ``Swap`` expresses that the values at indexes ``J`` and ``K`` in
array ``X`` have been swapped:

.. code-block:: ada

   procedure Swap (X : in out Integer_Array; J, K : Positive) with
     Post => X = (X'Old with delta J => X'Old(K), K => X'Old(J));

and the postcondition of procedure ``Rotate_Clockwize_Z`` expresses that the
point ``P`` given in parameter has been rotated 90 degrees clockwise around the
Z axis (thus component ``Z`` is preserved while components ``X`` and ``Y`` are
modified):

.. code-block:: ada

   procedure Rotate_Clockwize_Z (P : in out Point_3D) with
     Post => P = (P'Old with delta X => P.Y'Old, Y => - P.X'Old);

Similarly to their use in combination with attribute ``Old`` in postconditions,
delta aggregates are useful in combination with :ref:`Attribute Loop_Entry`
inside :ref:`Loop Invariants`. For example, we can express the property that,
after iteration ``J`` in the main loop in procedure ``Zero_Range``, the value
of parameter array ``X`` at all indexes already seen is equal to zero:

.. code-block:: ada

   procedure Zero_Range (X : in out Integer_Array; From, To : Positive) is
   begin
      for J in From .. To loop
         X(J) := 0;
         pragma Loop_Invariant (X = (X'Loop_Entry with delta From .. J => 0));
      end loop;
   end Zero_Range;

Delta aggregates can also be used outside of assertions. They are particularly
useful in expression functions. For example, the functionality in procedure
``Rotate_Clockwize_Z`` could be expressed equivalently as an expression
function:

.. code-block:: ada

   function Rotate_Clockwize_Z (P : Point_3D) return Point_3D is
     (P with delta X => P.Y, Y => - P.X);

Because it requires copying the value of ``P``, the type of ``P`` cannot be
limited.

.. note::

   In |SPARK| versions up to |SPARK| 21, delta aggregates are not supported
   and an equivalent attribute named ``Update`` can be used instead.

*Specific to SPARK*

As a GNAT-specific extension for SPARK (which requires the use of switch
``-gnatX0`` or pragma ``Extensions_Allowed(All)``), it is also possible to use
subcomponents as choices in a delta aggregate. In the following example, the
postcondition of procedure ``Zero_Left_Of_Pair_At_Index`` uses a delta
aggregate to specify that parameter ``P`` is updated by setting the ``Left``
component of its element at index ``I`` to zero:

.. code-block:: ada

   type Pair is record
      Left, Right : Integer;
   end record;

   type Index is range 1 .. 10;
   type Pairs is array (Index) of Pair;

   procedure Zero_Left_Of_Pair_At_Index (P : in out Pairs; I : Index) with
     Post => P = (P'Old with delta (I).Left => 0);

The subcomponent should be designated by a chain of indexes in parentheses (for
indexing into arrays) and component names (for accessing into records, with a
dot preceding the component name if this not the first subcomponent). Such
choices can be used together with the usual choices that designate a top-level
component.

.. index:: Aspect Aggregate

Aspect Aggregate
^^^^^^^^^^^^^^^^

*Supported in Ada 2022*

The ``Aggregate`` aspect has been introduced in
`Ada 2022 <http://www.ada-auth.org/standards/22rm/html/RM-4-3-5.html>`_.
It allows providing subprograms that can be used to create aggregates of a
particular container type. The required subprograms differ depending on the
kind of aggregate being defined - positional, named, or indexed. Only positional
and named container aggregates are allowed in SPARK. They require supplying
an ``Empty`` function, to create the container, and an ``Add`` procedure to
insert a new element (possibly associated to a key) in the container:

.. code-block:: ada

   --  We can use positional aggregates for sets
   type Set_Type is private
      with Aggregate => (Empty       => Empty_Set,
                         Add_Unnamed => Include);
   function Empty_Set return Set_Type;
   procedure Include (S : in out Set_Type; E : Element_Type);

   --  and named aggregates for maps
   type Map_Type is private
      with Aggregate =>  (Empty     => Empty_Map,
                          Add_Named => Add_To_Map);
   function Empty_Map return Map_Type;
   procedure Add_To_Map (M     : in out Map_Type;
                         Key   : Key_Type;
                         Value : Element_Type);

For execution, container aggregates are expanded into a call to the ``Empty``
function, followed by a sequence of calls to the ``Add`` procedure. However,
for proof, this is not appropriate. Due to how VC generation works, instructions
cannot be used to expand expressions occurring in annotations in particular.
In addition, such an expansion would be inefficient in terms of provability, as
it would introduce multiple intermediate values on which the provers need to
reason.

To be able to use container aggregates in proof, additional annotations are
necessary. They describe how the information supplied by the aggregate - the
elements, the keys, their order, the number of elements... - affects the
value of the container after the insertions. It works by supplying additional
functions that should be used to describe the container. These functions and
their intended usage are recognized using an
:ref:`Annotation for Container Aggregates`.

Container aggregates follow the Ada 2022 syntax for homogeous aggregates. The
values, or associations for named aggregates, are enclosed in square brackets.
As an example, here are a few aggregates for functional and formal containers
from the :ref:`SPARK Libraries`.

.. code-block:: ada

   package Integer_Sets is new SPARK.Containers.Formal.Ordered_Sets (Integer);
   S : Integer_Sets.Set := [1, 2, 3, 4, 12, 42];

   package String_Lists is new
     SPARK.Containers.Formal.Unbounded_Doubly_Linked_Lists (String);
   L : String_Lists.List := ["foo", "bar", "foobar"];

   package Int_To_String_Maps is new
     SPARK.Containers.Functional.Maps (Integer, String);
   M : Int_To_String_Maps.Map := [1 => "one", 2 => "two", 3 => "three"];

.. note::

   So the handling is as precisely as possible, |SPARK| only
   supports aggregates with distinct values or keys for sets and maps.

.. index:: if-expression, case-expression

Conditional Expressions
-----------------------

*Supported in Ada 2012*

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

.. index:: declare-expression

Declare Expressions
-------------------

*Supported in Ada 2022*

Declare expressions are used to factorize parts of an expression. They allow to
declare constants and renamings which are local to the expression. A
declare expression is made of two parts:

* A list of declarations of local constants and renamings
* An expression using the names introduced in these declarations.

To match the syntax of declare blocks, the first part is introduced by
``declare`` and the second by ``begin``. The scope is delimited by enclosing
parentheses, without ``end`` to close the scope.

As an example, we introduce a ``Find_First_Zero`` function which finds the index
of the first occurrence of ``0`` in an array of integers and a procedure
``Set_Range_To_Zero`` which zeros out all elements located between the first
and second occurrence of ``0`` in the array:

.. code-block:: ada

   function Has_Zero (A : My_Array) return Boolean is
     (for some E of A => E = 0);

   function Has_Two_Zeros (A : My_Array) return Boolean is
     (for some I in A'Range => A (I) = 0 and
        (for some J in A'Range => A (J) = 0 and I /= J));

   function Find_First_Zero (A : My_Array) return Natural with
     Pre  => Has_Zero (A),
     Post => Find_First_Zero'Result in A'Range
       and A (Find_First_Zero'Result) = 0
       and not Has_Zero (A (A'First .. Find_First_Zero'Result - 1));

   procedure Set_Range_To_Zero (A : in out My_Array) with
     Pre  => Has_Two_Zeros (A),
     Post =>
        A = (A'Old with delta
               Find_First_Zero (A'Old) ..
                 Find_First_Zero
	           (A'Old (Find_First_Zero (A'Old) + 1 .. A'Last)) => 0);

In the contract of ``Set_Range_To_Zero``, we use :ref:`Delta Aggregates` to
state that elements of ``A`` located in the range between the first and the
second occurrence of ``0`` in ``A`` have been set to ``0`` by the procedure.
The second occurrence is found by calling ``Find_First_Zero``
on the slice of ``A`` starting just after the first occurrence of ``0``.

To make the contract of ``Set_Range_To_Zero`` more readable, we can use a
declare expression to introduce constants for the first and second occurrence
of ``0`` in the array. The explicit names make it easier to understand what the
bounds of the updated slice are supposed to be. It also avoids repeating the
call to ``Find_First_Zero`` on ``A`` in the computation of
the second bound:

.. code-block:: ada

   procedure Set_Range_To_Zero (A : in out My_Array) with
     Pre  => Has_Two_Zeros (A),
     Post =>
       (declare
          Fst_Zero : constant Positive := Find_First_Zero (A'Old);
          Snd_Zero : constant Positive := Find_First_Zero
	     (A'Old (Fst_Zero + 1 .. A'Last));
        begin
          A = (A'Old with delta Fst_Zero .. Snd_Zero => 0));

.. index:: expression function
           Gold level; expression function

Expression Functions
--------------------

*Supported in Ada 2012*

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

.. index:: ghost code
           see: Ghost; ghost code
           Gold level; ghost code
           Platinum level; ghost code

Ghost Code
----------

*Specific to SPARK*

Sometimes, the variables and functions that are present in a program are not
sufficient to specify intended properties and to verify these properties with
|GNATprove|. In such a case, it is possible in |SPARK| to insert in the program
additional code useful for specification and verification, specially identified
with the aspect ``Ghost`` so that it can be discarded during
compilation. So-called `ghost code` in |SPARK| are these parts of the code that
are only meant for specification and verification, and have no effect on the
functional behavior of the program.

Note that assertions (including contracts) are not necessarily ghost code. A
contract on a ghost entity is considered as ghost code, while a contract on a
non-ghost entity is not. Depending on the corresponding value of
``Assertion_Policy`` (of kind ``Ghost`` for ghost code, of kind ``Assertions``
for all assertions, or of more specific assertion kinds like ``Pre`` and
``Post``), ghost code and assertions are executed or ignored at runtime.

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
* `Ghost generic formal parameters` are used to pass on ghost entities (types,
  objects, subprograms, packages) as parameters in a generic instantiation.
* `Ghost models` work as an abstraction layer by providing a simplified view of
  complex part of the program that can be used in contracts.
* `Non-executable ghost code` represents concepts that cannot (easily) be
  computed in the implementation.

When the program is compiled with assertions (for example with switch
``-gnata`` in |GNAT Pro|), ghost code is executed like normal code. Ghost code
can also be selectively enabled by setting pragma ``Assertion_Policy`` as
follows:

.. code-block:: ada

   pragma Assertion_Policy (Ghost => Check);

or through :ref:`Assertion Levels`.

|GNATprove| checks that ghost code cannot have an effect on the behavior of the
program. If pragma ``Assertion_Policy`` is used to disable some ghost code while
retaining other, |GNATprove| also makes sure that no disabled ghost entity is
used in enabled ghost code - so the program can compile - and that disabled
ghost code cannot have an effect on enabled ghost entities - so the program
always behaves as if all ghost code was enabled and the verification remains
sound. |GNAT Pro| compiler also performs some of these checks, although not
all of them. Apart from these checks, |GNATprove| treats ghost code like normal
code during its analyses.

Ghost Functions
^^^^^^^^^^^^^^^

Ghost functions are useful to express properties only used in contracts, and to
factor out common expressions used in contracts. For example, function
``Get_Total`` introduced in :ref:`Abstraction and Functional Contracts`
to retrieve the value of variable ``Total`` in the contract of ``Add_To_Total``
could be marked as a ghost function as follows:

.. code-block:: ada

   function Get_Total return Integer with Ghost;

and still be used exactly as seen in :ref:`Abstraction and Functional
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
Containers Library` in the |SPARK| library typically copy the entire content of
the argument container, which would not be acceptable for non-ghost functions.

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
     Post => Log_Size = Log_Size'Old + 1 and Log = (Log'Old with delta Log_Size => Incr);

   procedure Add_To_Total (Incr : in Integer) is
   begin
      Total := Total + Incr;
      Log_Size := Log_Size + 1;
      Log (Log_Size) := Incr;
   end Add_To_Total;

The postcondition of ``Add_To_Total`` above expresses that ``Log_Size`` is
incremented by one at each call, and that the current value of parameter
``Incr`` is appended to ``Log`` at each call (using :ref:`Attribute Old` and
:ref:`Delta Aggregates`).

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
     Post => Log_Size = Log_Size'Old + 1 and Log = (Log'Old with delta Log_Size => Incr);

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
        Post => Log_Size = Log_Size'Old + 1 and Log = (Log'Old with delta Log_Size => Incr);

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

Ghost Generic Formal Parameters
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Non-ghost generic units may depend on ghost entities for the specification and
proof of their instantiations. In such a case, the ghost entities can be passed
on as ghost generic formal parameters:

.. code-block:: ada

   generic
      type T is private with Ghost;
      Var_Input  : T with Ghost;
      Var_Output : in out T with Ghost;
      with function F return T with Ghost;
      with procedure P (X : in out T) with Ghost;
      with package Pack is new Gen with Ghost;
   package My_Generic with
     SPARK_Mode
   is
      ...

At the point of instantiation of ``My_Generic``, actual parameters for ghost
generic formal parameters may be ghost, and in three cases, they must actually
be ghost: the actual for a mutable ghost generic formal object, a ghost generic
formal procedure, or a ghost generic formal package, must be ghost. Otherwise,
writing to a ghost variable or calling a ghost procedure could have an effect
on non-ghost variables.

.. code-block:: ada

   package My_Instantiation is
     new My_Generic (T          => ... -- ghost or not
                     Var_Input  => ... -- ghost or not
                     Var_Output => ... -- must be ghost
                     F          => ... -- ghost or not
                     P          => ... -- must be ghost
                     Pack       => ... -- must be ghost

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

Non-Executable Ghost Code
^^^^^^^^^^^^^^^^^^^^^^^^^

It is possible to define entities
that are not meant to be executed at all. This is useful to represent concepts
that are useful in specification but that we cannot - or don't want to -
compute at runtime. This might include logical concepts, such as unbounded
quantification - using :ref:`Aspect and Pragma Iterable` - or logical equality
(see :ref:`Annotation for Accessing the Logical Equality for a Type`), as well
as parts of the program whose model is not accessible from the language, for
example the file system (see :ref:`Input-Output Libraries`) or a memory model.

To be usable inside contracts, these concepts need to be declared as Ada
entities but their body or actual representation does not
matter as they are not meant to be executed. In particular, ghost subprograms
might be marked as imported, so an error will be raised at link time if a
call is inadvertently enabled, or their bodies might be marked as SPARK_Mode Off
and raise an exception. Ghost state might be represented using an abstract state
on a package whose body is Off with no refinement or thanks to a private type
with a dummy definition. It is possible to use non-executable
:ref:`Assertion Levels` to ensure that such ghost code is never enabled at
runtime.

For example, the ghost procedure ``Append_To_Log`` seen previously may be
defined equivalently as a ghost imported function as follows:

.. code-block:: ada

   function Append_To_Log (Log : Log_type; Incr : in Integer) return Log_Type with
     Ghost,
     Import;

where ``Log_Type`` is a private type whose actual defintion is hidden from
|GNATprove|. This
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

Note that non-executable ghost subprograms should be used with care as
|GNATprove| will not attempt to verify them as it does not have access to an
implementation.

Assertion Levels
^^^^^^^^^^^^^^^^
As explained in SPARK RM 11.4.3, assertion levels can be used to group
together ghost entities, contracts, and assertions that can be enabled or
disabled together through an ``Assertion_Policy`` pragma. As an example, in the
following snippet, it makes it possible to disable together the definition of
``X`` and the first assertion while retaining the rest of the ghost code:

.. code-block:: ada

   pragma Assertion_Policy (L2 => Check);
   pragma Assertion_Policy (L1 => Ignore);

   X : Integer := 12 with Ghost => L1;
   Y : Integer := 0  with Ghost => L2;

   pragma Assert (L1 => X = 12);
   pragma Assert (L2 => Y = 0);

There are two predefined assertion levels: ``Runtime`` and ``Static``. The
``Runtime`` level is always enabled whereas the ``Static`` level is always
ignored. As an example, they can be used in the following snippet to get the
same behavior as in the example above, and so, no matter what compiler options
or ``Assertion_Policy`` pragmas are used.

.. code-block:: ada

   X : Integer := 12 with Ghost => Static;
   Y : Integer := 0  with Ghost => Runtime;

   pragma Assert (Static  => X = 12);
   pragma Assert (Runtime => Y = 0);

It is possible for users to declare their own assertion level using the
``Assertion_Level`` pragma at the configuration level. However, it should be
used with care, as such levels are visible everywhere, which might lead to
conflicts particularly when using libraries. To avoid this issue, it might be
interesting to define a shared project defining assertion levels for all related
libraries and to use explicit names.

.. code-block:: ada

   pragma Assertion_Level (L1);
   pragma Assertion_Level (L2);

When assertion levels are used, |GNATprove| enforces level-based compatibility
rules in addition to the policy-based compatibility rules explained at the
beginning of :ref:`Ghost Code`. For example, using a ghost variable ``X`` of
level ``L1`` inside an assertion of an unrelated assertion level ``L2`` is
rejected. These rules ensure that enabling or disabling an assertion level won't
cause the code to stop compiling.

.. code-block:: ada

   X : Integer := 12 with Ghost => L1;
   pragma Assert (L1 => X = 12);  --  Rejected

If ghost entities or assertions do not have
an associated assertion level, then they are not subject to the
level-based compatibility rules. The policy-based rules remain though.

.. code-block:: ada

   pragma Assertion_Policy (L => Ignore);

   X : Integer := 12 with Ghost => L;

   pragma Assertion_Policy (Assert => Ignore);
   pragma Assert (X = 12);  --  Accepted

   pragma Assertion_Policy (Assert => Check);
   pragma Assert (X = 12);  --  Rejected

When declaring an assertion level, it is possible to give a list of levels it
depends on as follows:

.. code-block:: ada

   pragma Assertion_Level (Silver);
   pragma Assertion_Level (Gold, Depends => Silver);
   pragma Assertion_Level (Platinum, Depends => [Gold, Static]);

An assertion level can only be enabled if all the levels it depends on are
enabled too. This is enforced automatically in the following way:

  * Enabling a level through ``Assertion_Policy`` also enables all levels
    it depends on. For example, enabling ``Gold`` would automatically enable
    ``Silver``.

  * Disabling a level through ``Assertion_Policy`` also disables all levels
    that depend on it. So, disabling ``Silver`` would automatically disable
    ``Gold``.

This property makes it possible to use an entity of a given level inside a
context of a level that depends on it. For example, it would be possible to use
an entity of level ``Silver`` in an assertion of level ``Gold``. It is similar
to the possibility of referencing a non-ghost entity from a (necessarily ghost)
assertion. Dependency is transitive, so here ``Platinum`` also depends on
``Silver`` even if it is implicit.

As explained before, the ``Static`` assertion level cannot be enabled at
runtime. As per the rules above, it is also the case of all levels that depend
on ``Static``, like ``Platinum`` for example. Static and the levels that depend
on it can be used in particular for :ref:`Non-Executable Ghost Code`, to ensure
that it is never enabled at runtime.

For the purpose of level-based
compatibility rules, levels depending on ``Static`` are handled specifically. In
particular, it is possible to use any ghost entity in the context of such a
level. Indeed, as such levels can never be enabled at runtime, it does not
matter whether entities referred in it are enabled or not. For example, it is
OK to use an entity of levels ``L1`` or ``Silver`` in an assertion of level
``Static`` even if ``Static`` does not depend on these levels:

.. code-block:: ada

   X : Integer := 12 with Ghost => L1;
   Y : Integer := 12 with Ghost => Silver;
   pragma Assert (Static => X = Y); --  Accepted

Removal of Ghost Code
^^^^^^^^^^^^^^^^^^^^^

By default, |GNAT Pro| completely discards ghost code during compilation, so
that no ghost code is present in the object code or the executable.
This is essential in domains submitted to certification where all
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
executable. For example on Unix-like platforms::

  nm <object files or executable> | grep my_unit

.. index:: quantified-expression

Quantified Expressions
----------------------

*Supported in Ada 2012*

A quantified expression is a way to express a property over a collection,
either an array or a container (see :ref:`Formal Containers Library`):

* a `universally quantified expression` using ``for all`` expresses a property
  that holds for all elements of a collection
* an `existentially quantified expression` using ``for some`` expresses a
  property that holds for at least one element of a collection

Quantified expressions should always be parenthesized.

Iteration Over Content vs. Over Positions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Iteration can be expressed either directly over the content of the collection,
or over the range of positions of elements in the collection. The former is
preferred when the property involved does not refer to the position of elements
in the collection or to the previous value of the element at the same position
in the collection (e.g. in a postcondition). Otherwise, the latter is
needed. For example, consider the procedure ``Nullify_Array`` that sets each
element of its array parameter ``X`` to zero. Its postcondition can be
expressed using a universally quantified expression iterating over the content
of the array as follows:

.. code-block:: ada

   procedure Nullify_Array (X : out Integer_Array) with
     Post => (for all E in X => E = 0);

or using a universally quantified expression iterating over the range of the
array as follows:

.. code-block:: ada

   procedure Nullify_Array (X : out Integer_Array) with
     Post => (for all J in X'Range => X(J) = 0);

Quantification over formal containers can similarly iterate over their content,
using the syntax ``for .. of``, or their positions, using the syntax
``for .. in``, see examples in :ref:`Loop Examples`.

Iteration over positions is needed when the property refers to the position of
elements in the collection. For example, consider the procedure
``Initialize_Array`` that sets each element of its array parameter ``X`` to its
position. Its postcondition can be expressed using a universally quantified
expression as follows:

.. code-block:: ada

   procedure Initialize_Array (X : out Integer_Array) with
     Post => (for all J in X'Range => X(J) = J);

Iteration over positions is also needed when the property refers to the
previous value of the element at the same position in the collection.
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

Execution vs. Proof
^^^^^^^^^^^^^^^^^^^

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

Iterator Filters
^^^^^^^^^^^^^^^^

The set of values or positions over which iteration is performed can be
filtered with an `iterator filter` introduced by the keyword ``when``. For
example, we can express a property for all prime numbers in a given range as
follows:

.. code-block:: ada

    (for all N in 1 .. 1000 when Is_Prime (N) => ...)
