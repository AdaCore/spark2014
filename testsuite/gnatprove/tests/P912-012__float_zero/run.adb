package body Run
with SPARK_Mode => On
is

   procedure Test_Float_Greater (X1, X2 : in T_Float_Value;
                                 Y : out T_Float) is
   begin
      Y := X2 - X1;
   end Test_Float_Greater;

   procedure Test_Float_Difference_Greater (X1, X2 : in T_Float_Value;
                                 Y : out T_Float) is
   begin
      Y := X2 - X1;
   end Test_Float_Difference_Greater;

   procedure Test_Float_Different (X1, X2 : in T_Float_Value;
                                   Y : out T_Float) is
   begin
      Y := X2 - X1;
   end Test_Float_Different;

   procedure Test_Float_Difference (X1, X2 : in T_Float_Value;
                                    Y : out T_Float) is
   begin
      Y := X2 - X1;
   end Test_Float_Difference;

end Run;
