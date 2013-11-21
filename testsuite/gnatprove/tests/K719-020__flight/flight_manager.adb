package body Flight_Manager is

   function Set_Engine_Speed
     (Position_X, Position_Y : Integer; Target_X, Target_Y : Integer)
      return Engine_Values
   is
      Result : Engine_Values;

      procedure Adjust_Speed
        (F : in out Integer; Distance_To_Target : Integer);

      procedure Adjust_Speed
        (F : in out Integer; Distance_To_Target : Integer) is
      begin
         if Distance_To_Target < 10 then
            F := (F * Distance_To_Target) / 10;
         end if;
      end Adjust_Speed;

      function My_Abs (I : Integer) return Integer is
      begin
         if I < 0 then
            return -I;
         else
            return I;
         end if;
      end My_Abs;

   begin
      if Position_X > Target_X then
         Result.X_Speed := -100;
      elsif Position_X < Target_X then
         Result.X_Speed := 100;
      end if;

      if Position_Y > Target_Y then
         Result.Y_Speed  := -100;
      elsif Position_Y < Target_Y then
         Result.Y_Speed  := 100;
      end if;

      Adjust_Speed (Result.X_Speed, My_Abs (Position_X - Target_X));
      Adjust_Speed (Result.Y_Speed, My_Abs (Position_Y - Target_Y));

      return Result;
   end Set_Engine_Speed;

end Flight_Manager;

