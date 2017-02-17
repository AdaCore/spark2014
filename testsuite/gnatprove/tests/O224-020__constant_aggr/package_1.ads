package Package_1
with SPARK_Mode => On
is
   type Record_T is
      record
         A : Float;
         B : Float;
      end record;

   Scalar_Const : constant Float := 0.01;
   Record_Const : constant Record_T :=
      Record_T'(A => 7.0,
                B => 12.0);

   procedure Procedure_1 (Res_1 :    out Float;
                          Res_2 :    out Float;
                          Res_3 :    out Float);

end Package_1;
