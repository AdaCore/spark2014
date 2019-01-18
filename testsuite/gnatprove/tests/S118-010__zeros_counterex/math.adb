package body Math with SPARK_Mode => On is

   Two_Thirds                  : constant Float := 2.0 / 3.0;
   One_Third                   : constant Float := 1.0 / 3.0;
   One_Div_By_Square_Root_Of_3 : constant Float := 0.57735;

   function Clarke_Transform (Input : Stationary_3_Phase_Vector)
                              return Stationary_2_Phase_Vector is

      A1 : constant Float := Two_Thirds * Input.A;
      A2 : constant Float := One_Third * Input.B;
      A3 : constant Float := One_Third * Input.C;

      pragma Assert (abs A1 <= 8.2 * 2.0 / 3.0);
      pragma Assert (abs A2 <= 8.2 / 3.0);
      pragma Assert (abs A3 <= 8.2 / 3.0);

      B1 : constant Float := One_Div_By_Square_Root_Of_3 * Input.B;
      B2 : constant Float := One_Div_By_Square_Root_Of_3 * Input.C;

      pragma Assert (abs B1 <= 8.2 * One_Div_By_Square_Root_Of_3);
      pragma Assert (abs B2 <= 8.2 * One_Div_By_Square_Root_Of_3);

   begin
      return (Alfa => A1 - A2 - A3,
              Beta => B1 - B2);
   end Clarke_Transform;

end Math;
