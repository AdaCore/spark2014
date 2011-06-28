Verification Goals
==================

GNATprove generates Verification Conditions (VCs) whose proof ensures that some
property holds on the source program. Such VCs can be generated to ensure
different high-level properties of the code, annotations and their combination.

Completeness of Preconditions
-----------------------------

This is currently the only verification activity available with GNATprove, in
mode ``check``. It consists in verifying that preconditions of subprograms can
never raise a run-time error, whatever the calling context. In order to get
such a good property on the preconditions he writes, the user should in general
guard all expressions which may raise a ``Constraint_Error`` in Ada, such as
array accesses and arithmetic operations.

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
   p.ads:7:31: (info) proved: division by zero
   p.ads:10:31: (info) proved: division by zero
   p.ads:13:15: (info) proved: division by zero

Notice also that division might also overflow here, if ``X`` is the minimal
integer value and ``Y`` is ``-1`` (standard 32-bits integers are assumed
here). GNATprove generates VCs to check this overflow, and it detects that only
the precondition of the last of these specifications cannot raise a run-time
error::

   p.ads:4:15: overflow check failed
   p.ads:7:31: overflow check failed
   p.ads:10:31: overflow check failed
   p.ads:13:15: (info) proved: overflow check

Absence of Run-Time Errors *(In Progress)*
-------------------------------------------

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

Functional Verification *(In Progress)*
-------------------------------------

GNATprove generates VCs to prove that all subprograms called in the code of a
subprogram analyzed have their precondition satisfied at the point of call, and
that the postcondition of the subprogram analyzed is satisfied.

In order to prove such VCs, the user may have to write loop invariants, for
which specific VCs are generated, to prove that the loop invariant is initially
valid (*loop invariant initiation*) and that it is preserved through the loop
(*loop invariant preservation*).

Consistency Checks *(Not Yet Implemented)*
------------------------------------------

Like code, contracts are written by a human and thus can contain errors.
GNATprove helps detecting inconsistencies in contracts by implementing specific
checks for the following cases: redundant annotations, inconsistent
annotations, unimplementable contracts, incomplete contracts. These checks
do not detect all problematic cases, only some of them, much like detection of
dead code by static analysis.

Redundant Annotations *(Not Yet Implemented)*
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A logical annotation (precondition, postcondition, assertion) should always be
non-redundant, that is, no part of the annotation should be trivially true or
false in the context of the complete annotation. Consider the following
specification::

   procedure Q (X, Y : in out Integer) with 
     Pre  => X > 0 and X > 0;

Here, the programmer mistyped ``X`` for ``Y``, which makes the precondition
redundant. At worst, the annotation may be tautological (always true), which
makes it much easier to prove, and also completely useless to express anything
interesting about a subprogram. Consider the following specification::

   function Max (X, Y : Integer) return Integer with 
     Post => (if X < Y then Max'Result = Y)
              or (if X >= Y then Max'Result = X);

This postcondition could be read as "if ``X`` is less than ``Y``, then function
``Max`` returns ``Y``, or in the other case where ``X`` is greater or equal to
``Y``, ``Max`` returns ``X``". The problem is that this postcondition is always
true, whatever function ``Max`` returns. To see it, consider the abstract form
of the postcondition
  
  (if A then B) or (if (not A) then C)

It can be rewritten as

  ((not A) or B) or (A or C)

which is the same as

  A or (not A) or B or C

which is always true! The programmer used ``or`` where he should have used
``and`` in the postcondition. GNATprove will detect such (partially or
completely) redundant annotations and issue a warning to the programmer.

Inconsistent Annotations *(Not Yet Implemented)*
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A logical annotation (precondition, postcondition, assertion) should always be
consistent, that is, is should not be always false. Consider the following
specification::

   procedure P (X, Y : in out Integer) with 
     Pre  => X <= 0 and X > 0;

Here, the programmer mistyped ``X`` for ``Y``, which makes the precondition
inconsistent. While inconsistent assertions and postconditions lead to
unprovable VCs when proving the subprogram, inconsistent preconditions can only
be detected this way when proving the caller. It is much better to detect such
cases earlier when proving the subprogram, as a *precondition* that is always
false makes the corresponding subprogram trivially *correct*, because under
this false hypothesis, everything can be proved. GNATprove will detect such
inconsistent annotations and issue an error to the programmer.

Unimplementable Contracts *(Not Yet Implemented)*
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A contract should express in its precondition all restrictions under which a
subprogram can possibly (maybe not always) deliver a proper service. This means
that, given an input respecting the precondition, there should be a possible
output respecting the postcondition. If this is not the case, then the
subprogram is unimplementable. Consider the following specification::

   procedure Compute (X : in Integer; Y : out Integer) with
     Post => (if X >= 0 then Y = 1) and (if X <= 0 then Y = -1);

An implementation of ``Compute`` with this contract is unlikely to be
provable. If it is, that's only because ``Compute`` never returns on input
``X=0``. Indeed, if ``Compute`` did return on input ``X=0``, it would have to
satisfy inconsistent requirements that ``Y=1`` and ``Y=-1``. Therefore, the
precondition should specify here that ``X/=0`` in input. GNATprove will detect
such unimplementable contracts and issue an error to the programmer.

Incomplete Contracts *(Not Yet Implemented)*
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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
contribute to establishing the postcondition. 

GNATprove will report this situation as a warning, indicating which portions of
the code do not contribute to the subprogram contract. The programmer can then
either correct the contract to reflect both situations, remove the offending
portion of the code, or accept the warning.

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
programmer.

