package body My_Pack with SPARK_Mode => Off is
   procedure Change_X is
   begin
      X := not X;
   end Change_X;
begin
   X := True;
end My_Pack;
