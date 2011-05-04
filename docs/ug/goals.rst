Verification Goals
==================

GNATprove generates Verification Conditions (VCs) whose proof ensures that some
property holds on the source program. Such VCs can be generated to ensure
different high-level properties of the code, annotations and their combination.

Completeness of Preconditions
-----------------------------

This is currently the only verification activity available with GNATprove. It
consists in verifying that preconditions of subprograms can never raise a
run-time error, whatever the calling context. In order to get such a good
property on the preconditions he writes, the user should in general guard all
expressions which may raise a ``Constraint_Error`` in Ada, such as array
accesses and arithmetic operations.

These guards may take the form desired by the user. In particular, no guard is
necessary if the operation cannot raise a run-time error, e.g. due to the
ranges of variables involved. As an example, consider the following subprogram
specifications::

   procedure Not_Guarded (X, Y : Integer) with
     Pre => X / Y > 0;

   procedure Guarded_And_Then (X, Y : Integer) with
     Pre => Y /= 0 and then X / Y > 0;

   procedure Guarded_If_Then (X, Y : Integer) with
     Pre => (if Y /= 0 then X / Y > 0);

   procedure No_Need_For_Guard (X, Y : Positive) with
     Pre => X / Y > 0;

GNATprove is able to show that only the precondition of the first of these
specifications could raise a run-time error::

   p.ads:4:15: division by zero failed
   p.ads:7:31: Proved - division by zero
   p.ads:10:31: Proved - division by zero
   p.ads:13:15: Proved - division by zero

Notice also that division might also overflow here, if ``X`` is the minimal
integer value and ``Y`` is ``-1`` (standard 32-bits integers are assumed
here). GNATprove generates VCs to check this overflow, and it detects that only
the precondition of the last of these specifications cannot raise a run-time
error::

   p.ads:4:15: range check failed
   p.ads:7:31: range check failed
   p.ads:10:31: range check failed
   p.ads:13:15: Proved - range check

Note that the current version of GNATprove misclassifies those as range checks.

Absence of Run-Time Errors *(In Progress)*
--------------------------

GNATprove generates VCs to prove that the code of a subprogram analyzed does
not contain violations of the following checks:

* overflow check
* range check
* array bound check
* division by zero check

In order to prove such VCs, the user may have to write loop invariants, for
which specific VCs are generated, to prove that the loop invariant is initially
valid (*loop invariant initiation*) and that it is preserved through the loop
(*loop invariant preservation*).

Functional Properties *(In Progress)*
---------------------

GNATprove generates VCs to prove that all subprograms called in the code of a
subprogram analyzed have their precondition satisfied at the point of call, and
that the postcondition of the subprogram analyzed is satisfied.

In order to prove such VCs, the user may have to write loop invariants, for
which specific VCs are generated, to prove that the loop invariant is initially
valid (*loop invariant initiation*) and that it is preserved through the loop
(*loop invariant preservation*).

Absence of Unintended Functionality *(TO DO)*
-----------------------------------

Redundant Specifications *(TO DO)*
------------------------

