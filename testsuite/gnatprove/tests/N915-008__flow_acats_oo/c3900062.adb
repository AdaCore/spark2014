

     --==================================================================--


with C3900060;            -- Basic alert abstraction.

with Ada.Calendar;
pragma Elaborate (Ada.Calendar);

package body C3900062 is

   use C3900060;  -- Enumeration values directly visible.
   use C3900061;  -- Extended alert system abstraction.


   procedure Assign_Officer (MA : in out Medium_Alert_Type;
                             To : in     Person_Enum) is
   begin
      MA.Action_Officer := To;
   end Assign_Officer;


   procedure Handle (MA : in out Medium_Alert_Type) is
   begin
      Handle (Low_Alert_Type (MA));      -- Call parent's op (type conversion).
      Set_Level (MA, 2);                 -- Call inherited operation.
      Assign_Officer (MA, Duty_Officer); -- Call newly declared operation.
      Set_Display (MA, Console);         -- Call inherited operation.
      Display (MA);                      -- Call doubly inherited operation.
   end Handle;


   function Initial_Values_Okay (MA : in Medium_Alert_Type) return Boolean is
   begin
      -- Call parent's operation (type conversion).
      return (Initial_Values_Okay (Low_Alert_Type (MA)) and
              MA.Action_Officer = Nobody);
   end Initial_Values_Okay;


   function Bad_Final_Values (MA : in Medium_Alert_Type) return Boolean is
      use type Ada.Calendar.Time;
   begin
      return (Get_Time(MA)      /= Alert_Time or
              Get_Display(MA)   /= Console    or
              Get_Level(MA)     /= 2          or
              MA.Action_Officer /= Duty_Officer);
   end Bad_Final_Values;


end C3900062;
