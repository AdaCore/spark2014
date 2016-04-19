with Ada.Real_Time; use Ada.Real_Time;

package body Concurrency_Example_Fixed_Bis is

   protected body Data is
      function Get return Integer is
         V : constant Integer := Ext_Data;
      begin
         return V;
      end Get;

      procedure Set (V : Integer) is
      begin
         Ext_Data := V;
      end Set;
   end Data;

   task body Writer is
      Flip   : Boolean := True;
      Wakeup : Time    := Clock;
   begin
      loop
         if Flip then
            Data.Set (1);
         else
            Data.Set (0);
         end if;
         Wakeup := Wakeup + Seconds (1);
         delay until Wakeup;
      end loop;
   end Writer;

   task body Reader is
      Value  : Integer;
      Wakeup : Time := Clock;
   begin
      loop
         Value := Data.Get;
         --  do some work with value read
         Wakeup := Wakeup + Seconds (1);
         delay until Wakeup;
      end loop;
   end Reader;

end Concurrency_Example_Fixed_Bis;
