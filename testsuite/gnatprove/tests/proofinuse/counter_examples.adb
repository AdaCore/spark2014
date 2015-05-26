package body Counter_Examples with
  SPARK_Mode
is

   procedure Float_Last (X, Y : Float; Res : out Float) is
   begin
      pragma Assume (Y <= 0.0);
      pragma Assume (X <= Float'Last + Y);
      Res := X - Y;  --  @OVERFLOW_CHECK:FAIL
   end Float_Last;

   procedure Upper_Multiple_Of_64
     (B   :     Boolean;
      X   :     Unsigned_32;
      Res : out Unsigned_32) is
   begin
      Res := ((X + 63) / 64) * 64;
      if B then
         pragma Assert (Res <= X);  --  @ASSERT:FAIL
      else
         pragma Assert (Res >= X);  --  @ASSERT:FAIL
      end if;
   end Upper_Multiple_Of_64;

end Counter_Examples;
