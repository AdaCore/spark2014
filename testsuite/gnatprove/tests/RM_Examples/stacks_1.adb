package body Stacks_1
  with SPARK_Mode
is
   function Is_Empty (S : Stack_Type) return Boolean is (S.Pointer = 0);
   --  Default Refined_Post => Is_Empty'Result = S.Pointer = 0
   --  refines the postcondition of True in terms of the full view of
   --  Stack_Type.

   function Is_Full (S : Stack_Type) return Boolean is
     (S.Pointer = Stack_Size);
   --  Default Refined_Post => Is_Full'Result = (S.Pointer = Stack_Size)
   --  refines the postcondition of True in terms of the full view of
   --  Stack_Type.

   procedure Push (S : in out Stack_Type; I : in Integer)
     with Refined_Post => S.Pointer = S.Pointer'Old + 1 and
          S.Vector = (S.Vector'Old with delta S.Pointer => I)
     --  Refined_Post in terms of full view of Stack_Type and a
     --  further constraint added specifying what is required by the
     --  implementation.
   is
   begin
      S.Pointer := S.Pointer + 1;
      S.Vector (S.Pointer) := I;
   end Push;

   procedure Pop (S : in out Stack_Type)
     with Refined_Post => S.Pointer = S.Pointer'Old - 1
     --  Refined_Post in terms of full view of Stack_Type and also
     --  specifies what is required by the implementation.
   is
   begin
      if S.Pointer > 0 then
         S.Pointer := S.Pointer - 1;
      end if;
   end Pop;

   function Top (S : Stack_Type) return Integer is (S.Vector (S.Pointer));
   --  Default Refined_Post => Top'Result = S.Vector (S.Pointer)
   --  refines the postcondition of True in terms of the full view of
   --  Stack_Type.
end Stacks_1;
