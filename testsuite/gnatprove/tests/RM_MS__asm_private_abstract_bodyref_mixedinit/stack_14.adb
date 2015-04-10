package body Stack_14
  with SPARK_Mode,
       Refined_State => (Stack => (S, Pointer)) -- state refinement
is
   Stack_Size : constant := 100;
   type    Pointer_Range is range 0 .. Stack_Size;
   subtype Index_Range   is Pointer_Range range 1..Stack_Size;
   type    Vector        is array(Index_Range) of Integer;

   S       : Vector; -- left uninitialized
   Pointer : Pointer_Range := 0;
   -- initialization by elaboration of declaration

   procedure Push(X : in Integer)
     with Refined_Global => (In_Out => (S, Pointer))
   is
   begin
      Pointer := Pointer + 1;
      S (Pointer) := X;
   end Push;

   procedure Pop (X : out Integer)
     with Refined_Global => (Input  => S,
                             In_Out => Pointer)
   is
   begin
      X := S (Pointer);
      Pointer := Pointer - 1;
   end Pop;
begin
   -- partial initialization by body statements
   S := (Index_Range => 0);
end Stack_14;
