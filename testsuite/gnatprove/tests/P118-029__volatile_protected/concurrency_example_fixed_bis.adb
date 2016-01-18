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
      Flip     : Boolean := True;
      Cur_Time : Time    := Clock;
   begin
      loop
         if Flip then
            Data.Set (1);
         else
            Data.Set (0);
         end if;
         delay until Cur_Time + Seconds (1);
      end loop;
   end Writer;

   task body Reader is
      Value    : Integer;
      Cur_Time : Time := Clock;
   begin
      loop
         Value := Data.Get;
         --  do some work with value read
         delay until Cur_Time + Seconds (1);
      end loop;
   end Reader;

end Concurrency_Example_Fixed_Bis;
