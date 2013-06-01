.. _usage scenarios for formal verification:

***************************************
Usage Scenarios for Formal Verification
***************************************

..  Note that, in many cases, ad-hoc data structures based on pointers can be
    replaced by the use of standard Ada containers (vectors, lists, sets, maps,
    etc.) Although the implementation of standard containers is not in |SPARK|,
    we have defined a slightly modified version of these targeted at formal
    verification. These formal containers are implemented in the GNAT standard
    library. These alternative containers are typical of the tradeoffs implicit
    in |SPARK|: favor automatic formal verification as much as possible, at the
    cost of minor adaptations to the code.

To be completed

|GNATprove| generates Verification Conditions (VCs) whose proof ensures that some
property holds on the source program. Such VCs are generated for functional
properties expressed as annotations but also to ensure different high-level
properties of the code described in the subsequent sections.

.. _completeness of preconditions:

Completeness of Preconditions
-----------------------------

This verification activity is part of the proof analysis of |GNATprove|.  It
consists in verifying that preconditions of subprograms can never raise a
run-time error, whatever the calling context. In order to get such a good
property on the preconditions, the user should in general guard all expressions
which may raise a ``Constraint_Error`` in Ada, such as array accesses and
arithmetic operations.

These guards may take the form desired by the user. In particular, no guard is
necessary if the operation cannot raise a run-time error, e.g. due to the
ranges of variables involved. As an example, consider the following subprogram
specifications:

.. code-block:: ada
   :linenos:

   procedure Not_Guarded (X, Y : Integer) with
     Pre => X / Y > 0;

   procedure Guarded_And_Then (X, Y : Integer) with
     Pre => Y /= 0 and then X / Y > 0;

   procedure Guarded_If_Then (X, Y : Integer) with
     Pre => (if Y /= 0 then X / Y > 0);

   procedure No_Need_For_Guard (X, Y : Positive) with
     Pre => X / Y > 0;

|GNATprove| is able to show that only the precondition of the first of these
specifications could raise a run-time error::

   p.ads:4:15: division check not proved
   p.ads:7:31: (info) division check proved
   p.ads:10:31: (info) division check proved
   p.ads:13:15: (info) division check proved

Notice also that division might also overflow here, if ``X`` is the minimal
integer value and ``Y`` is ``-1`` (standard 32-bits integers are assumed
here). |GNATprove| checks this overflow condition, and it detects that only
the precondition of the last of these specifications cannot raise a run-time
error::

   p.ads:4:15: overflow check not proved
   p.ads:7:31: overflow check not proved
   p.ads:10:31: overflow check not proved
   p.ads:13:15: (info) overflow check proved

.. _absence of run-time errors:

Absence of Run-Time Errors
--------------------------

This verification activity is available in mode ``prove``.
|GNATprove| verifies that the code of a subprogram analyzed does not contain
violations of the following checks:

* overflow check
* range check
* index check
* division check
* discriminant check
* length check

The precise meaning of these checks is given by the Ada Language Reference
Manual. An (*overflow check*) violation occurs when the result of an arithmetic
operation cannot be represented in the base type (usually a machine integer)
for this operation. A (*range check*) violation occurs when a value does not
respect the range constraint for its type. An (*index check*) violation occurs
when the value used to index into an array does not fit between the array
bounds. A (*division check*) violation occurs when the divisor of a division
operation (or ``rem`` or ``mod``) is zero. A *discriminant check* violation
occurs when the discriminant(s) of a discriminant record does not have the
expected value for a given operation. A *length check* violation occurs when an
array does not have the expected length.

Note that |GNATprove| also takes into account checks that occur in assertions
and pre- and postconditions.

.. _functional verification:

Functional Verification
-----------------------

This verification activity is available in mode ``prove``.  |GNATprove| generates
VCs to prove that all subprograms called in the code of a subprogram analyzed
have their precondition satisfied at the point of call. It also generates VCs
to prove that the postcondition of the subprogram analyzed is satisfied.

In order to prove such VCs, the user may have to write loop invariants, for
which specific VCs are generated, to prove that the loop invariant is initially
valid (*loop invariant initiation*) and that it is preserved through the loop
(*loop invariant preservation*).

