package body adt_private_refinement_14 is
   function Is_Empty(S : Stack) return Boolean
   with
      Refined_Post => Is_Empty'Result = (S.Stack_Pointer = 0)
   is
   begin
      return S.Stack_Pointer = 0;
   end Is_Empty;

   function Is_Full(S : Stack) return Boolean 
   with
      Refined_Post => Is_Full'Result = (S.Stack_Pointer = Stack_Size)
   is
   begin
      return S.Stack_Pointer = Stack_Size;
   end Is_Full;

   procedure Clear(S : out Stack)
   with
      Refined_Post => (Is_Empty(S),
                       S.Stack_Pointer = 0,
                       (for all I in Index_Range => (S.Stack_Vector(I) = 0)))
   is
   begin
      S.Stack_Pointer := 0;
      S.Stack_Vector  := Vector'(Index_Range => 0);
   end Clear;

   procedure Push(S : in out Stack; X : in Integer) 
   with
      Refined_Post => (not Is_Empty(S),
	               S.Stack_Pointer = S'Old.Stack_Pointer + 1,
	               S.Stack_Vector = S'Old.Stack_Vector'Update(S.Stack_Pointer => X))
   is
   begin
      S.Stack_Pointer := S.Stack_Pointer + 1;
      S.Stack_Vector(S.Stack_Pointer) := X;
   end Push;

   procedure Pop(S : in out Stack; X : out Integer) 
   with
      Refined_Post => (not Is_Full(S),  
                       X = S.Stack_Vector(S'Old.Stack_Pointer),
	               S.Stack_Pointer = S'Old.Stack_Pointer - 1)
   is
   begin
      X := S.Stack_Vector(S.Stack_Pointer);
      S.Stack_Pointer := S.Stack_Pointer - 1;
   end Pop;
end adt_private_refinement_14;
