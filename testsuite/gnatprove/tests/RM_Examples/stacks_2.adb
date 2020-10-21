package body Stacks_2
  with SPARK_Mode,
       Refined_State => (The_Stack => (A_Pointer, A_Vector))
is
   --  Constituents of state abstraction The_Stack
   --  We promised to initialize The_Stack
   A_Pointer : Pointer_Type := 0;
   A_Vector  : Stack_Array := (others => 0);

   --  Is_Empty could have been written as a expression function as was done
   --  for Is_Empty (S : Stack_Type) but is presented here as a subproram body
   --  to contrast the two approaches
   function Is_Empty return Boolean
     with Refined_Global => A_Pointer,
          Refined_Post   => Is_Empty'Result = (A_Pointer = 0)
     --  Refines the postcondition of True in terms of the constituent A_Pointer.
   is
   begin
      return A_Pointer = 0;
   end Is_Empty;

   --  Could be written as an expression function
   function Is_Full return Boolean
     with Refined_Global => A_Pointer,
          Refined_Post   => Is_Full'Result = (A_Pointer = Stack_Size)
     --  Refines the postcondition of True in terms of the constituent A_Pointer.
   is
   begin
      return A_Pointer = Stack_Size;
   end Is_Full;

   procedure Push (I : Integer)
     with Refined_Global => (In_Out => (A_Pointer, A_Vector)),
          Refined_Post   => A_Pointer = A_Pointer'Old + 1 and
                            A_Vector = (A_Vector'Old with delta A_Pointer => I)
     --  Refined_Post in terms of constituents A_Pointer and A_Vector and a further
     --  constraint added specifying what is required by the implementation.
   is
   begin
      A_Pointer := A_Pointer + 1;
      A_Vector (A_Pointer) := I;
   end Push;

   procedure Pop
     with Refined_Global => (In_Out => A_Pointer),
          Refined_Post   => A_Pointer = A_Pointer'Old - 1
     --  Refined_Post in terms of constituents A_Pointer and also
     --  specifies what is required by the implementation.
   is
   begin
      A_Pointer := A_Pointer - 1;
   end Pop;

   function Top return Integer is (A_Vector (A_Pointer))
     with Refined_Global => (A_Pointer, A_Vector);
   --  Default Refined_Post => Top'Result = A_Vector (S.Pointer)
   --  refines the postcondition of True in terms of the constituents
   --  A_Pointer and A_Vector.
end Stacks_2;
