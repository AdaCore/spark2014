pragma SPARK_Mode;

with Ada.Unchecked_Conversion;

procedure Zero_And_Min
is
   procedure Crash (A, B : Float)
   is
      function Magic is new Ada.Unchecked_Conversion (Float, Integer);
      X : constant Integer := Magic (Float'Min (A, B));
      Y : constant Integer := Magic (Float'Min (B, A));
   begin
      if X /= Y then
         pragma Assert (Float'Min (A, B) /= Float'Min (B, A));
      end if;
   end Crash;

   type UInt32 is mod 2 ** 32;
   function Convert is new Ada.Unchecked_Conversion (UInt32, Float);

   Zero_Plus : constant Float := Convert (16#0000_0000#);
   Zero_Neg  : constant Float := Convert (16#8000_0000#);

begin

   Crash (Zero_Plus, Zero_Neg);

end Zero_And_Min;
