package body Simple
with SPARK_Mode
is

   procedure Mammals (A : Animal) is
   begin
      pragma Assert (A /= chicken);
   end Mammals;

end Simple;
