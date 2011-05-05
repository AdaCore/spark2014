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

Functional Behavior *(In Progress)*
-------------------

GNATprove generates VCs to prove that all subprograms called in the code of a
subprogram analyzed have their precondition satisfied at the point of call, and
that the postcondition of the subprogram analyzed is satisfied.

In order to prove such VCs, the user may have to write loop invariants, for
which specific VCs are generated, to prove that the loop invariant is initially
valid (*loop invariant initiation*) and that it is preserved through the loop
(*loop invariant preservation*).

Absence of Unintended Functionality *(Not Yet Implemented)*
-----------------------------------

A general concern in safety and security standards is the absence of unintended
functionality. When verification relies on testing, this is sometimes verified
by showing that tests implementing the low-level requirements achieve complete
code coverage. With formal verification, we can aim at a different,
higher-level goal: show that all the code in a subprogram contributes to
establishing its postcondition. This is not the same as saying that a contract
entirely summarizes the purpose of a subprogram, as the contract might still be
an abstraction of the subprogram's behavior. But if some code is useless to
establish the subprogram's postcondition, the contract is either wrong or
incomplete. To illustrate the issue, consider the following procedure sketch::

   procedure P (X : Integer) with
     Pre => (...),
     Post => (if X = 0 then ...);

   procedure P (X : Integer) is
   begin
      if X = 0 then
         --  Do something when X = 0
      else
         --  Do something else otherwise
      end if;
   end P;

Here, the problem is that the contract only states the behavior of the
procedure when ``X`` is equal to zero, but not what happens when this is
not the case. This means that the entire ``else`` branch does not
contribute to establishing the postcondition. This introduces a semantic
notion of *dead code*: the code in the ``else`` branch is *dead* in the
sense that outside the procedure ``P``, no other part of the code should
take advantage of the effects in that branch.

GNATprove will report this situation, indicating which portion of the code
is *dead* in this sense. The programmer can then either correct the contract
to reflect both situations or remove the offending portion of the code.

Another case of incomplete specifications is illustrated by the following
simple program::

   procedure Full_Stop with
     Pre  => (...),
     Post => (Accel = 0);

   procedure Full_Stop is
   begin
      Accel  := 0;
      Breaks := On;
   end Full_Stop;

In this example, the contract is again incomplete: it only mentions that the
acceleration is set to zero, but not that the breaks are activated. Said
otherwise, it only mentions the modification of the ``Accel`` variable,
but not the one of ``Breaks``. Again, a warning will be issued to the
programmer, stating that a written variable is not mentioned in the contract,
so no other part of the program can be aware of its new value, and this is
probably a bug either in the code or in the contract.

Redundant Specifications *(Not Yet Implemented)*
------------------------

A common case of meaningless specifications is the case of trivial or
redundant assertions. An assertion that is always false or always true is not
very useful. Worse, a *precondition* that is always false (or
*inconsistent*) makes the corresponding subprogram trivially *correct*,
because under this false hypothesis, everything can be proved.  Similarly, a
postcondition that is always true can be proved correct, but it certainly does
not express anything interesting about the subprogram. GNATprove will detect
such undesirable annotations and issue a warning to the programmer.
