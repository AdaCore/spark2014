package body Across_Compilation_Units is
   procedure Swap (X, Y: in out Integer)
   is
      Temp : Integer;
   begin
      Temp := X;
      X := Y;
      Y := Temp;
   end;

   procedure Swap_With_Depends (X, Y: in out Integer)
   is
      Temp : Integer;
   begin
      Temp := X;
      X := Y;
      Y := Temp;
   end;
end Across_Compilation_Units;
