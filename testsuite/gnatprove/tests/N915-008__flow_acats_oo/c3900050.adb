

     --==================================================================--


package body C3900050 is  -- Alert system abstraction.


   procedure Set_Display (A : in out Alert_Type;
                          D : in     Device_Enum) is
   begin
      A.Display_On := D;
   end Set_Display;


   procedure Display (A : in Alert_Type) is
   begin
      Display_Count_For (A.Display_On) := Display_Count_For (A.Display_On) + 1;
   end Display;


   procedure Handle (A : in out Alert_Type) is
   begin
      A.Arrival_Time := Alert_Time;
      Display (A);
   end Handle;


   function Get_Time (A: Alert_Type) return Ada.Calendar.Time is
   begin
      return A.Arrival_Time;
   end Get_Time;


   function Get_Display (A: Alert_Type) return Device_Enum is
   begin
      return A.Display_On;
   end Get_Display;


   function Initial_Values_Okay (A : in Alert_Type) return Boolean is
   begin
      return (A = (Arrival_Time => Default_Time,         -- Check "=" operator
                   Display_On   => Null_Device));        -- availability.
   end Initial_Values_Okay;                              -- Aggregate with
                                                         -- named associations.

   function Bad_Final_Values (A : in Alert_Type) return Boolean is
   begin
      return (A /= (Alert_Time, Null_Device));           -- Check "/=" operator
                                                         -- availability.
   end Bad_Final_Values;                                 -- Aggregate with
                                                         -- positional assoc.

end C3900050;
