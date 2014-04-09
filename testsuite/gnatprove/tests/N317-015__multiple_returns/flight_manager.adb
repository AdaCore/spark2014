package body Flight_Manager with
  SPARK_Mode
is

   function Set_Engine_Speed
     (Position_X, Position_Y : Integer; Target_X, Target_Y : Integer)
      return Integer
   is
      function My_Abs (I : Integer) return Integer;
      function My_Abs (I : Integer) return Integer is
      begin
         if I < 0 then
            return -I;
         else
            return I;
         end if;
      end My_Abs;

      Max : Integer;
   begin
      Max := My_Abs (Position_X - Target_X);
      return Max;
   end Set_Engine_Speed;

end Flight_Manager;
