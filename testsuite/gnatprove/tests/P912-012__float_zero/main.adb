with Run;
with Ada.Text_IO; use Ada.Text_IO;

procedure Main
  with SPARK_Mode => Off
is
   Y_Float_Test_Greater, Y_Float_Test_Different, Y_Float_Test_Difference, Y_Float_Test_Difference_Greater : Run.T_Float;
begin
   Run.Test_Float_Greater (X1 => 5.0,
                           X2 => 10.0,
                           Y  => Y_Float_Test_Greater);
   Run.Test_Float_Different (X1 => 5.0,
                             X2 => 10.0,
                             Y  => Y_Float_Test_Different);
   Run.Test_Float_Difference (X1 => 5.0,
                             X2 => 10.0,
                             Y  => Y_Float_Test_Difference);
   Run.Test_Float_Difference_Greater (X1 => 5.0,
                             X2 => 10.0,
                             Y  => Y_Float_Test_Difference_Greater);
   Put_Line ("Y_Float_Test_Greater = " & Run.T_Float'Image (Y_Float_Test_Greater));
   Put_Line ("Y_Float_Test_Different = " & Run.T_Float'Image (Y_Float_Test_Different));
   Put_Line ("Y_Float_Test_Difference = " & Run.T_Float'Image (Y_Float_Test_Difference));
   Put_Line ("Y_Float_Test_Difference_Greater = " & Run.T_Float'Image (Y_Float_Test_Difference_Greater));
end Main;
