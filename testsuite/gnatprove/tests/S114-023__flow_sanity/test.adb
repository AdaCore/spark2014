package body Test
with
   Refined_State => (Valid => State_Valid, State => Time_Info)
is

   Time_Info : Integer := 0;

   procedure Get_Current_Time
     (Schedule_Ticks :     Integer;
      Correction     : out Integer)
   is
   begin
      null;
   end Get_Current_Time;

end Test;
