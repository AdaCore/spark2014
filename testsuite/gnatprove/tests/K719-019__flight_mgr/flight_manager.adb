package body Flight_Manager is

   function Set_Engine_Speed
     (Position_X, Position_Y : Float; Target_X, Target_Y : Float)
      return Engine_Values
   is
      Result : Engine_Values;

      procedure Adjust_Speed
        (F : in out Float; Distance_To_Target : Float) with
        Post =>
          (if Distance_To_Target < 10.0 then
            F = (F'Old * Distance_To_Target) / 10.0);

      procedure Adjust_Speed
        (F : in out Float; Distance_To_Target : Float) is
      begin
         if Distance_To_Target < 10.0 then
            F := (F * Distance_To_Target) / 10.0;
         end if;
      end Adjust_Speed;

   begin
      if Position_X > Target_X then
         Result.X_Speed := -100.0;
      elsif Position_X < Target_X then
         Result.X_Speed := 100.0;
      end if;

      if Position_Y > Target_Y then
         Result.Y_Speed  := -100.0;
      elsif Position_Y < Target_Y then
         Result.Y_Speed  := 100.0;
      end if;

      Adjust_Speed (Result.X_Speed, abs (Position_X - Target_X));
      Adjust_Speed (Result.Y_Speed, abs (Position_Y - Target_Y));

      return Result;
   end Set_Engine_Speed;

end Flight_Manager;
