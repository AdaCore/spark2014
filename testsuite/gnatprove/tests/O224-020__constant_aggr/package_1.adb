package body Package_1
   with SPARK_Mode => On
is
   procedure Procedure_1 (Res_1 :    out Float;
                          Res_2 :    out Float;
                          Res_3 :    out Float)
   is
      Temp : constant Float := Record_Const.A;
   begin
      Res_1 := Scalar_Const + Scalar_Const;
      Res_2 := Scalar_Const + Record_Const.A;
      Res_3 := Scalar_Const + Temp;
   end Procedure_1;

end Package_1;
