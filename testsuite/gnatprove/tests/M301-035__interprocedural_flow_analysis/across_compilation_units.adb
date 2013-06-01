package body Across_Compilation_Units is
   function Prime (X: Natural) return Boolean is
   begin
      for I in 2 .. X / 2 loop
         if (X mod I) = 0 then
            return False;
         end if;
      end loop;
      return True;
   end Prime;

   procedure Swap (X, Y: in out Integer) is
      Temp : Integer;
   begin
      Temp := X;
      X := Y;
      Y := Temp;
   end Swap;

   procedure Swap_With_Depends (X, Y: in out Integer) is
      Temp : Integer;
   begin
      Temp := X;
      X := Y;
      Y := Temp;
   end Swap_With_Depends;
end Across_Compilation_Units;
