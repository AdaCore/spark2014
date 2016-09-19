.. _GNATprove_Limitations:

|GNATprove| Limitations
=======================

.. _Tool Limitations:

Tool Limitations
----------------

#. The Global contracts generated automatically by |GNATprove| for subprograms
   without an explicit one do not take into account indirect calls (through
   access-to-subprogram and dynamic binding) and indirect reads/writes to
   global variables (through access variables).

#. A subset of all Ada conversions between array types is supported:

   * element types must be exactly the same
   * matching index types must either be both modular with a base type of the
     same size, or both non modular

#. A subset of all Ada fixed-point types and fixed-point operations is
   supported:

   * fixed-point types must have a small that is a negative power of 2 or 10
   * multiplication and division between different fixed-point types and
     universal real are rejected
   * multiplication and division whose result type is not the same fixed-point
     type as its fixed-point argument(s) are rejected, except for the special
     case of dividing a fixed-point value by the small of its type
     (T'Small) to yield an integer result which is always exact.

   These restrictions ensure that the result of fixed-point operations always
   belongs to the *perfect result set* as defined in Ada RM G.2.3.

#. Loop_Invariant and Loop_Variant pragmas must appear before
   any non-scalar object declaration and any nested loop.

#. Inheriting the same subprogram from multiple interfaces is not supported.

#. Formal object parameters of generics of an unconstrained record type with
   per-object constrained fields are badly supported by the tool and may
   result in crashes in some cases.

#. Quantified expressions with an iterator over a multi dimensional array (for
   example ``for all Elem of Arr`` where ``Arr`` is a multi dimensional array)
   are not supported.

#. Constrained subtypes of class-wide types and 'Class attributes of
   constrained record types are not supported.

#. Abstract states cannot be marked ``Part_Of`` a single task declaration or a
   single protected declaration (see |SPARK| RM 9(3)). An error is raised
   instead in such cases.

#. Classwide Global and Depends contracts as defined in SPARK RM 6.1.6 are not
   supported.

#. Task attributes Identity and Storage_Size are not supported.

#. Type_Invariant and Invariant aspects are not supported:

   * on private types declared in nested packages or child packages
   * on protected types
   * on tagged types
   * on components of tagged types if the tagged type is visble from inside the
     scope of the invariant bearing type.

Legality Rules
--------------

#. |SPARK| Reference Manual rule 4.3(1), concerning use of the box
   symbol "<>" in aggregates, is not currently checked.

#. The elaboration order rules described in the |SPARK| Reference
   Manual 7.7 are not currently checked.

#. The rule concerned with asserting that all child packages which
   have state denoted as being Part_Of a more visible state
   abstraction are given as constituents in the refinement of the more
   visible state is not checked (|SPARK| Reference Manual rule
   7.2.6(6)).

#. |GNATprove| does not permit formal parameters to be mentioned
   in the ``input_list`` of an Initializes Aspect, contrary
   to |SPARK| Reference Manual 7.1.5(4). This limitation is only
   relevant for packages that are nested inside subprograms.
   This limitation is corrected in versions of the toolset based
   on GNAT Pro 7.2.2, GPL 2014, or later.

#. The case of a state abstraction whose Part_Of aspect denotes a
   task or protected unit is not currently supported.

#. The case of a Refined_Post specification for a (protected) entry
   is not currently supported.

#. The use Ada.Synchronous_Barriers.Synchronous_Barrier type is not currently
   allowed in |SPARK|.

#. Entry families are not currently allowed in |SPARK|.

Flow Analysis Limitations
-------------------------

#. Flow dependencies caused by record assignments is not captured with perfect
   accuracy. This means that the value of one field might incorrectly be
   considered to participate in the derivation of another field that it does
   not really participate in.

Proof Limitations
-----------------

#. Postconditions of recursive functions called in contracts and assertion
   pragmas are not available, possibly leading to unproved checks. The current
   workaround is to use a non-recursive wrapper around those functions.

#. Attribute 'Valid is currently assumed to always return True.

#. Values read from an external source are assumed to be valid values.
   Currently there is no model of invalidity or undefinedness. The onus
   is on the user to ensure that all values read from an external source are
   valid. The use of an invalid value invalidates any proofs associated with
   the value.

#. The following attributes are not yet supported in proof: Adjacent, Aft,
   Bit_Order, Body_Version, Copy_Sign, Definite, Denorm, First_Valid, Fore,
   Last_Valid, Machine, all Machine_* attributes, Model, all Model_* attributes,
   Partition_Id, Remainder, Round, Safe_First, Safe_Last, Scale, Scaling, Small,
   Unbiased_Rounding, Version, Wide_Image, Wide_Value, Wide_Width,
   Wide_Wide_Image, Wide_Wide_Value, Wide_Wide_Width, Width.

   The attributes First_Bit, Last_Bit and Position are supported but if there is
   no record representation clause then we assume that their value is
   nonnegative.

#. The 'Update attribute on multidimensional unconstrained arrays is not
   yet fully supported in proof. Checks might be missing so currently an
   error is emitted for any use of the 'Update attribute on
   multidimensional unconstrained arrays.

#. The difference between the floating-point values +0 and -0 (as defined in
   IEEE-754 standard) is ignored in proof. This is correct for all programs that
   do not exploit the difference in bit-pattern between +0 and -0. For example,
   the following specially crafted program is proved by |GNATprove| but fails at
   run time due to a division by zero, because function ``Magic`` exploits the
   difference of bit-pattern between +0 and -0 by using ``Unchecked_Conversion``
   to return a different integer value for arguments +0 and -0.

   .. code-block:: ada

      pragma SPARK_Mode;

      with Ada.Unchecked_Conversion;

      procedure Zero_And_Unchecked is
         procedure Crash (A, B : Float) is
            function Magic is new Ada.Unchecked_Conversion (Float, Integer);
            X : Integer;
         begin
            if A = B then
               if Magic (B) /= 0 then
                  X := 100 / Magic (A);
               end if;
            end if;
         end Crash;

         type UInt32 is mod 2 ** 32;
         function Convert is new Ada.Unchecked_Conversion (UInt32, Float);

         Zero_Plus : constant Float := Convert (16#0000_0000#);
         Zero_Neg  : constant Float := Convert (16#8000_0000#);
      begin
         Crash (Zero_Plus, Zero_Neg);
      end Zero_And_Unchecked;

#. |GNATprove| does not follow the value of tags for tagged objects. As a
   consequence, tag checks are currently unprovable in most cases.

#. Constants declared in loops before the loop invariant are handled as
   variables by the tool. This means in particular that any information
   about their values needed after the loop invariant must be stated explicitly
   in the loop invariant.

#. Preconditions on arithmetic and conversion operators (including Time_Of) in
   Ada.Execution_Time and Ada.Real_Time packages described in |SPARK| Reference
   Manual 9.19 are not yet implemented.
