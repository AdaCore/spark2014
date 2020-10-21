package Arith_With_Local_Subp
  with SPARK_Mode
is
   procedure Add_Two (X : in out Integer) with
     Pre  => X <= Integer'Last - 2,
     Post => X = X'Old + 2;

end Arith_With_Local_Subp;
