package body Volatiles_Illegal_10
  with SPARK_Mode
is
   procedure Scalar_Formal_Parameter (Par : in out Vol_Scalar_T) is
   begin
      Par := Par + 1;
   end Scalar_Formal_Parameter;

   Obj : Vol_Scalar_T;

begin
   Scalar_Formal_Parameter (Obj);

end Volatiles_Illegal_10;
