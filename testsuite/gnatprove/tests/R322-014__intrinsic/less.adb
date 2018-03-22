with Import_Intrinsic;

function Less
  (X, Y : Import_Intrinsic.New_Float)
   return Boolean
   with SPARK_Mode
is
begin
   return Import_Intrinsic."<" (X, Y);
   --  Call to operator with SPARK_Mode => Off; should be rejected.
end Less;
