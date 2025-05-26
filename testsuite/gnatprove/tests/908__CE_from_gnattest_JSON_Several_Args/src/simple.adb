package body Simple
with SPARK_Mode
is

   procedure Several_Args (A, B, C, D : Integer) is
   begin
      pragma Assert (D mod 2 = 0);
   end Several_Args;

end Simple;
