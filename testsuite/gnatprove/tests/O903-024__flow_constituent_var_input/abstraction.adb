package body Abstraction with
   SPARK_Mode,
   Refined_State => (State => C)
is
   C : constant Integer := 0;

   procedure P is
      A : Integer := 4;
   begin
      null;
   end P;

end Abstraction;
