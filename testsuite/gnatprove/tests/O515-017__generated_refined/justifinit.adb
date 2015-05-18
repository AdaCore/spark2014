package body Justifinit
  with SPARK_Mode,
       Refined_State => (State => (X, Y))
is
   X, Y : Integer;

   procedure P
   --  with Refined_Global => (Output => (X, Y))
   is
   begin
      X := 0;
   end P;

end Justifinit;
