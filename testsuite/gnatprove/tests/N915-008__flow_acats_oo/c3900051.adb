

     --==================================================================--


with Ada.Calendar;
pragma Elaborate (Ada.Calendar);

package body C3900051 is  -- Extended alert system abstraction.

   use C3900050;  -- Alert system abstraction.


   procedure Set_Level (LA : in out Low_Alert_Type;
                        L  : in     Integer) is
   begin
      LA.Level := L;
   end Set_Level;


   procedure Handle (LA : in out Low_Alert_Type) is
   begin
      Handle (Alert_Type (LA));   -- Call parent's operation (type conversion).
      Set_Level (LA, 1);          -- Call newly declared operation.
      Set_Display (Alert_Type(LA),
                   Teletype);     -- Call parent's operation (type conversion).
      Display (LA);
   end Handle;


   function Get_Level (LA: Low_Alert_Type) return Integer is
   begin
      return LA.Level;
   end Get_Level;


   function Initial_Values_Okay (LA : in Low_Alert_Type) return Boolean is
   begin
      -- Call parent's operation (type conversion).
      return (Initial_Values_Okay (Alert_Type (LA)) and
              LA.Level = 0);
   end Initial_Values_Okay;


   function Bad_Final_Values (LA : in Low_Alert_Type) return Boolean is
      use type Ada.Calendar.Time;
   begin
      return (Get_Time(LA)    /= Alert_Time or
              Get_Display(LA) /= Teletype or
              LA.Level        /= 1);
   end Bad_Final_Values;


end C3900051;
