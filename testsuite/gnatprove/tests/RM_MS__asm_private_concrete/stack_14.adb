package body Stack_14
  with SPARK_Mode,
       Refined_State => (S_State       => S,
                         Pointer_State => Pointer)
is
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
end Stack_14;
