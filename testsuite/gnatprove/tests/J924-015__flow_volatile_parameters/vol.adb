package body Vol with
  SPARK_Mode
is
   procedure Assign (X : out T) is
   begin
      X.C := 1;
   end Assign;

   procedure Proc is
   begin
      Assign (V);
   end Proc;

end Vol;
