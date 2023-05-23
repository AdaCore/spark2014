.. index:: limitations

GNATprove Limitations
=====================

Tool Limitations that Impact Soundness
--------------------------------------

As these limitations may lead to soundness issues, users should review them to
ensure that their programs are not impacted.

* Checks related to tasking do not take into account dispatching calls.

Tool Limitations Leading to an Error Message
--------------------------------------------

.. include:: ../source/unsupported_constructs.rst

Other Tool Limitations
----------------------

The generation of Global contracts by |GNATprove| has limitations. When this
capability is used in a certification context, the generated contracts should
be verified by the user. In particular:

* The Global contracts generated automatically by |GNATprove| for subprograms
  without an explicit one, whose body is not in SPARK, do not take into account
  indirect calls (through access-to-subprogram and dynamic binding) and
  indirect reads/writes to global variables (through access variables). See
  :ref:`Coarse Generation for non-SPARK Subprograms`.

Some features defined in the reference manual have not been implemented in the
tool. It is the case of:

* classwide Global and Depends contracts as defined in SPARK RM 6.1.6, and

* the use of Ada.Synchronous_Barriers.Synchronous_Barrier type.

Flow Analysis Limitations
-------------------------

These limitations in the flow analysis part of GNATprove may result in a less
precise (but sound) analysis.

.. index:: Depends; limitation

* Flow dependencies caused by record assignments is not captured with perfect
  accuracy. This means that the value of one field might incorrectly be
  considered to participate in the derivation of another field that it does
  not really participate in.

.. index:: initialization; limitation

* Initialization of multi-dimensional arrays with nested FOR loops can be only
  detected if the array bounds are given by static expressions. A possible
  solution is to use :ref:`Aspect Relaxed_Initialization` instead in such a
  case and to prove that only initialized data is read.

Proof Limitations
-----------------

These limitations in the proof part of GNATprove may result in a less precise
(but sound) analysis.

.. index:: recursion; limitation

* Postconditions of possibly non-returning functions called in contracts and
  assertion pragmas are not available, which may lead to unproved
  checks. Using the switch ``--info`` reveals where the information about
  postcondition may be lost. The solution is to annotate the subprogram with
  the ``Always_Return`` annotation (see :ref:`Subprogram Termination`) which
  will be checked by GNATprove.

* The following attributes are not yet supported in proof: Adjacent, Aft,
  Bit_Order, Body_Version, Copy_Sign, Definite, Denorm, First_Valid, Fore,
  Last_Valid, Machine, all Machine_* attributes, Model, all Model_* attributes,
  Partition_Id, Remainder, Round, Safe_First, Safe_Last, Scale, Scaling, Small,
  Unbiased_Rounding, Version, Wide_Image, Wide_Value, Wide_Width,
  Wide_Wide_Image, Wide_Wide_Value, Wide_Wide_Width, Width.

  The attributes First_Bit, Last_Bit and Position are supported but if there is
  no record representation clause then we assume that their value is
  nonnegative.

.. index:: Loop_Invariant; limitation

* Constants declared in loops before the loop invariant are handled as
  variables by the tool. This means in particular that any information about
  their values needed after the loop invariant must be stated explicitly in the
  loop invariant.
