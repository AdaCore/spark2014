package body Counter_Examples with
  SPARK_Mode
is

   procedure Float_Last (X, Y : Float; Res : out Float) is
   begin
      pragma Assume (Y <= 0.0);
      pragma Assume (X <= Float'Last + Y);
      Res := X - Y;  --  @OVERFLOW_CHECK:FAIL
   end Float_Last;

end Counter_Examples;
