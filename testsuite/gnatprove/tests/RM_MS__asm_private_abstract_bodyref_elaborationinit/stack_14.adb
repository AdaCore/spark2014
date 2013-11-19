package body Stack_14
  with SPARK_Mode,
       Refined_State => (State => (Pointer, S)) -- refinement of state
is
   Stack_Size : constant := 100;
   type    Pointer_Range is range 0 .. Stack_Size;
   subtype Index_Range   is Pointer_Range range 1..Stack_Size;
   type    Vector        is array(Index_Range) of Integer;

   S : Vector := (others => 0);
   Pointer : Pointer_Range := 0;
   -- initialization by elaboration of declaration

   procedure Push(X : in Integer)
     with Refined_Global => (In_Out => (Pointer, S))
   is
   begin
      Pointer := Pointer + 1;
      S (Pointer) := X;
   end Push;

   procedure Pop(X : out Integer)
     with Refined_Global => (In_Out => Pointer,
                             Input  => S)
   is
   begin
      X := S (Pointer);
      Pointer := Pointer - 1;
   end Pop;
end Stack_14;
