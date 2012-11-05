package body Stack_14
   with Refined_State => (Stack => (S, Pointer)) -- state refinement
is
   S : Vector; -- left uninitialized
   Pointer : Pointer_Range := 0;
   -- initialization by elaboration of declaration

   procedure Push(X : in Integer)
      with Refined_Global => (In_Out => (S, Pointer))
   is
   begin
      Pointer := Pointer + 1;
      S(Pointer) := X;
   end Push;

   procedure Pop(X : out Integer)
      with Refined_Global => (Input  => S,
                              In_Out => Pointer)
   is
   begin
      X := S(Pointer);
      Pointer := Pointer - 1;
   end Pop;
begin  -- partial initialization by body statements
   S := Vector'(Index_Range => 0);
end Stack_14;
