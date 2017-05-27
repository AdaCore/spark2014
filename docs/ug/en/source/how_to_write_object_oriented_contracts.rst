.. _How to Write Object Oriented Contracts:

How to Write Object Oriented Contracts
======================================

Object Oriented Programming (OOP) may require the use of special
:ref:`Class-Wide Subprogram Contracts` for dispatching subprograms, so that
|GNATprove| can check Liskov Substitution Principle on every overriding
subprogram.

Object Oriented Code Without Dispatching
----------------------------------------

In the special case where OOP is used without dispatching, it is possible to
use the regular :ref:`Subprogram Contracts` instead of the special
:ref:`Class-Wide Subprogram Contracts`.

For example, consider a variant of the ``Logging`` and ``Range_Logging`` units
presented in :ref:`Class-Wide Subprogram Contracts`, where no dispatching is
allowed. Then, it is possible to use regular preconditions and postconditions
as contracts, provided ``Log_Type`` is publicly declared as an untagged private
type in both units:

.. literalinclude:: /gnatprove_by_example/examples/logging_no_dispatch.ads
   :language: ada
   :linenos:

.. literalinclude:: /gnatprove_by_example/examples/range_logging_no_dispatch.ads
   :language: ada
   :linenos:

Writing Contracts on Dispatching Subprograms
--------------------------------------------

Whenever dispatching is used, the contract that applies in proof to a
dispatching call is the class-wide contract, defined as the first one present
in the following list:

#. the class-wide precondition (resp. postcondition) attached to the subprogram
#. or otherwise the class-wide precondition (resp. postcondition) being
   inherited by the subprogram from the subprogram it overrides
#. or otherwise the default class-wide precondition (resp. postcondition) of
   ``True``.

For abstract subprograms (on interfaces or regular tagged types), only a
class-wide contract can be specified. For other dispatching subprograms, it is
possible to specify both a regular contract and a class-wide contract. In such
a case, |GNATprove| uses the regular contract to analyze static calls to the
subprogram and the class-wide contract to analyze dispatching calls to the
subprogram, and it checks that the specific contract is a refinement of the
class-wide contract, as explained in :ref:`Mixing Class-Wide and Specific
Subprogram Contracts`.

Let's consider the various cases that may occur when overridding a subprogram:

.. literalinclude:: /gnatprove_by_example/examples/geometry.ads
   :language: ada
   :linenos:

In package ``Geometry``, a type ``Shape`` is derived in a type ``Rectangle``. A
function ``Shape.Valid`` defines what it is to be a valid shape. It is
overridden by ``Rectangle.Valid`` which defines what it is to be a valid
rectangle. Here, a valid rectangle is also a valid shape, but that need not be
the case. Procedure ``Set_Default`` and its variants demonstrate the various
configurations that can be found in practice:

1. The overridden subprogram ``Shape.Set_Default`` defines a class-wide
   contract (here only a postcondition), which is inherited in the overriding
   subprogram ``Rectangle.Set_Default``. By the semantics of Ada, the
   postcondition of ``Shape.Set_Default`` calls ``Shape.Valid``, while the
   inherited postcondition of ``Rectangle.Set_Default`` calls
   ``Rectangle.Valid``.

2. Both the overridden subprogram ``Shape.Set_Default_Repeat`` and the
   overriding subprogram ``Rectangle.Set_Default_Repeat`` define a class-wide
   contract (here only a postcondition). Here, since the contract is simply
   repeated, this is equivalent to case 1 above of inheriting the contract: the
   postcondition of ``Shape.Set_Default_Repeat`` calls ``Shape.Valid``, while
   the postcondition of ``Rectangle.Set_Default_Repeat`` calls
   ``Rectangle.Valid``.

3. Only the overriding subprogram ``Rectangle.Set_Default_No_Post`` defines a
   class-wide contract (here only a postcondition). The default class-wide
   postcondition of ``True`` is used for the overridden
   ``Shape.Set_Default_No_Post``.

In case 1, the overriding subprogram satisfies Liskov Substitution Principle by
construction, so |GNATprove| emits no check in that case. Note that this is not
the same as saying that ``Shape.Set_Default`` and ``Rectangle.Set_Default``
have the same contract: here the two postconditions differ, as one calls
``Shape.Valid``, while the other calls ``Rectangle.Valid``.

In case 2, |GNATprove| checks that Liskov Substitution Principle is verified
between the contracts of the overridden and the overriding subprograms. Here,
it checks that the postcondition of ``Rectangle.Set_Default_Repeat`` is
stronger than the postcondition of ``Shape.Set_Default_Repeat``.

In case 3, |GNATprove| also checks that Liskov Substitution Principle is
verified between the default contract of the overridden subprogram and the
specified contract of the overriding subprograms. Here, only a postcondition is
specified for ``Rectangle.Set_Default_No_Post``, so it is indeed stronger than
the default postcondition of ``Shape.Set_Default_No_Post``.

Hence the results of |GNATprove|'s analysis on this program:

.. literalinclude:: /gnatprove_by_example/results/geometry.prove
   :language: none

Let's consider now calls to these subprograms in procedure ``Use_Geometry``:

.. literalinclude:: /gnatprove_by_example/examples/use_geometry.adb
   :language: ada
   :linenos:

Here are the results of |GNATprove|'s analysis on this program:

.. literalinclude:: /gnatprove_by_example/results/use_geometry.prove
   :language: none

Parameter ``S`` is of class-wide type ``Shape'Class``, so it can be dynamically
of both types ``Shape`` or ``Rectangle``. All calls on ``S`` are
dispatching. In this program, |GNATprove| needs to check that the precondition
of the calls to ``Operate`` is satisfied. As procedures ``Shape.Set_Default``
and ``Shape.Set_Default_Repeat`` state precisely this condition in
postcondition, the precondition to the calls to ``Operate`` that follow can be
proved. As procedure ``Shape.Set_Default_No_Post`` has no postcondition, the
precondition to the last call to ``Operate`` cannot be proved. Note that these
proofs take into account both possible types of ``S``, for example:

* If ``S`` is dynamically a shape, then the call to ``Shape.Set_Default`` on
  line 7 ensures that ``Shape.Valid`` holds, which ensures that the
  precondition to the call to ``Shape.Operate`` is satisfied on line 8.

* If ``S`` is dynamically a rectangle, then the call to
  ``Rectangle.Set_Default`` on line 7 ensures that ``Rectangle.Valid`` holds,
  which ensures that the precondition to the call to ``Rectangle.Operate`` is
  satisfied on line 8.

Writing Contracts on Subprograms with Class-wide Parameters
-----------------------------------------------------------

Subprograms with class-wide parameters are not in general dispatching
subprograms, hence they are specified through regular :ref:`Subprogram
Contracts`, not :ref:`Class-Wide Subprogram Contracts`. Inside the regular
contract, calls on primitive subprograms of the class-wide parameters are
dispatching though, like in the code. For example, consider procedure
``More_Use_Geometry`` which takes four class-wide parameters of type
``Shape'Class``, which can all be dynamically of both types ``Shape`` or
``Rectangle``:

.. literalinclude:: /gnatprove_by_example/examples/more_use_geometry.adb
   :language: ada
   :linenos:

The precondition of ``More_Use_Geometry`` specifies that ``S1.Valid`` holds,
which takes into account both possible types of ``S1``:

* If ``S1`` is dynamically a shape, then the precondition specifies that
  ``Shape.Valid`` holds, which ensures that the precondition to the call to
  ``Shape.Operate`` is satisfied on line 8.

* If ``S1`` is dynamically a rectangle, then the precondition specifies that
  ``Rectangle.Valid`` holds, which ensures that the precondition to the call to
  ``Rectangle.Operate`` is satisfied on line 8.

Similarly, the test on ``S2.Valid`` on line 10 ensures that the precondition to
the call to ``S2.Operate`` on line 11 is satisfied, and the call to
``S3.Set_Default`` on line 14 ensures through its postcondition that the
precondition to the call to ``S3.Operate`` on line 15 is satisfied. But no
precondition or test or call ensures that the precondition to the call to
``S4.Operate`` on line 17 is satisfied. Hence the results of |GNATprove|'s
analysis on this program:

.. literalinclude:: /gnatprove_by_example/results/more_use_geometry.prove
   :language: none
