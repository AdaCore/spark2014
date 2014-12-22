package Validation
  with SPARK_Mode
is
   Sequence_Length : constant Natural := 1000;

   subtype Index_T is Natural range 1 .. Sequence_Length;

   type Component_T is new Integer;

   type Arr_T is array (Index_T range <>) of Component_T;

   function Is_Valid (C : Component_T) return Boolean is
      (C in 2 .. 5);  --  arbitrary validation expression

   procedure Validate_Sequence (A : in Arr_T; Success : in out Boolean) with
     --  Note that the safety-oriented proof objective is the same whether
     --  the implementation is efficient (early exit) or not:
     --
     --  Determines (i.e. flags "not Success") if there are any invalid
     --  elements in the given array.
     Post => (if Success then
     (for all Index in A'Range => Is_Valid (A (Index))));

end Validation;
