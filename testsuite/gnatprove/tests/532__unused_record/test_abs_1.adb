with Ext; use Ext;
procedure Test_Abs_1 with SPARK_Mode is
   X : RR;

   function Eq (X, Y : RR) return Boolean is (X = Y);

begin
   pragma Assert (X.H = 1);
end Test_Abs_1;
