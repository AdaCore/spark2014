package body FP_Test_Div with
  SPARK_Mode
is
   procedure Test (X : FP1; Y : FP2; U : out FP3; V : out FP4) is
   begin
      U := X / Y;
      V := X / Y;
   end Test;

   procedure Test1 (X : FP1; Y : FP2; U : out FP3; V : out FP4) is
   begin
      U := X / Y;
      V := X / Y;
   end Test1;

   procedure Test2 (X : FP1; Y : FP2; U : out FP3; V : out FP4) is
   begin
      U := X / Y;
      V := X / Y;
   end Test2;

end FP_Test_Div;
