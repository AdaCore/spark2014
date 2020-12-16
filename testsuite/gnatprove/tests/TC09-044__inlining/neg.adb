procedure Neg is

   procedure Internal (V : Integer) is
   begin
      pragma Assert (-V > 0);
      pragma Assert (abs V > 0);
   end Internal;

begin
   Internal (Integer'First);
end Neg;
