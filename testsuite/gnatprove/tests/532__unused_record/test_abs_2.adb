with Ext; use Ext;
procedure Test_Abs_2 with SPARK_Mode is

   procedure Swap (X, Y : in out RR) is
      Tmp : RR := X;
   begin
      X := Y;
      Y := Tmp;
   end Swap;

begin
   null;
end Test_Abs_2;
