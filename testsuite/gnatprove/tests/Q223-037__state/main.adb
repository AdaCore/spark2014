with P;

--# inherit P;

--# main_program;

procedure Main
--# global out P.P_State;
  with SPARK_Mode,
       Global => (Output => P.P_Abs_State)
is
   X : Integer;
begin
   P.Set_Value (5);

   X := P.Calculate (10);

   P.Set_Value (X);

end Main;
