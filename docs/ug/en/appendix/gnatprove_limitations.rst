.. index:: limitations

GNATprove Limitations
=====================

Tool Limitations that Impact Soundness
--------------------------------------

As these limitations may lead to soundness issues, users should review them to
ensure that their programs are not impacted.

* Checks related to tasking do not take into account dispatching calls.

* Checks related to subprogram termination do not take into account dispatching
  calls.

* Calls occuring inside type invariants and subtype predicate are not taken into
  account by the verification tool while computing the call graph. This can in
  particular lead to soundness issues when such calls introduce recursion
  between subprograms.

* Cycles in the elaboration order between entities can lead to soundness issues.
  These cycles are generally detected during compilation. It might not be
  the case if such cycles are due to contracts and the program is compiled with
  assertions disabled.

* If a function annotated with an Ownership annotation assigns or declares
  an object of the related private type with Ownership either directly or
  inside a called subprogram, then the contract of the
  function might be used to prove itself, possibly resulting in a soundness
  issue if it is incorrect.

Other Tool Limitations
----------------------

These limitations correspond to limitations of the analysis that do not cause
soundness issues. When a construct is not supported, GNATprove issues an error
when analyzing the program.

* The Global contracts generated automatically by |GNATprove| for subprograms
  without an explicit one, whose body is not in SPARK, do not take into account
  indirect calls (through access-to-subprogram and dynamic binding) and
  indirect reads/writes to global variables (through access variables). See
  :ref:`Coarse Generation for non-SPARK Subprograms`.

* A subset of all Ada conversions between array types is supported:

  * element types must be exactly the same
  * matching index types must either be both modular with a base type of the
    same size, or both non modular

* A subset of all Ada fixed-point types and fixed-point operations is
  supported:

  * multiplication and division between different fixed-point types and
    floating-point types are rejected
  * multiplication and division between a fixed-point type and a real literal
    are rejected, the fix is to qualify the real literal with a fixed-point
    type as in ``Fp_Type'(0.25)``
  * multiplication and division between different fixed-point types are
    rejected if their smalls are not *compatible* as defined in Ada RM
    G.2.3(21)
  * conversions from fixed-point types to floating-point types are rejected

  These restrictions ensure that the result of fixed-point operations always
  belongs to the *perfect result set* as defined in Ada RM G.2.3.

* Multidimensional array types are supported up to 4 dimensions.

* Loop_Invariant and Loop_Variant pragmas must appear before any non-scalar
  object declaration.

* Inheriting the same subprogram from multiple interfaces is not supported.

* Quantified expressions with an iterator over a multi dimensional array (for
  example ``for all Elem of Arr`` where ``Arr`` is a multi dimensional array)
  are not supported.

* Constrained subtypes of class-wide types and 'Class attributes of
  constrained record types are not supported.

* Abstract states cannot be marked ``Part_Of`` a single concurrent object (see
  |SPARK| RM 9(3)).

* Classwide Global and Depends contracts as defined in SPARK RM 6.1.6 are not
  supported.

* Task attributes Identity and Storage_Size are not supported.

* Type_Invariant and Invariant aspects are not supported:

  * on private types declared in nested packages
  * on protected types
  * on tagged types
  * on components of tagged types if the tagged type is visible from inside the
    scope of the invariant bearing type.

* Calls to protected subprograms and protected entries whose prefix denotes a
  formal subprogram parameter are not supported. Similarly, suspension on
  suspension objects given as formal subprogram parameters is not supported.

* The case of a state abstraction whose Part_Of aspect denotes a task or
  protected unit is not currently supported.

* The case of a Refined_Post specification for a (protected) entry is not
  currently supported.

* The use of Ada.Synchronous_Barriers.Synchronous_Barrier type is not currently
  supported.

* Entry families are not currently supported.

* The 'Update attribute on multidimensional unconstrained arrays is not
  supported.

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
