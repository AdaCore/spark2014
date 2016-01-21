with Ada.Real_Time; use Ada.Real_Time;
with Ada.Text_IO;

package body Concurrency_Example_Fixed is

   protected body Data is
      function Get return Data_T is (Value);

      procedure Set (V : Data_T) is
      begin
         Value := V;
      end Set;
   end Data;

   task body Writer is
      Flip     : Boolean := True;
      Deadline : Time    := Clock;
   begin
      loop
         if Flip then
            Data.Set (All_Ones);
         else
            Data.Set (All_Zeroes);
         end if;
         Flip := not Flip;
         Deadline := Deadline + Milliseconds (10);
         delay until Deadline;
      end loop;
   end Writer;

   task body Reader is
      Value    : Data_T;
      Deadline : Time := Clock;
   begin
      loop
         Value := Data.Get;
         --  do some work with value read
         Ada.Text_IO.Put_Line (if Value = All_Zeroes then "all zeroes"
                               elsif Value = All_Ones then "all ones"
                               else "data race detected");
         pragma Assert (Value = All_Zeroes or Value = All_Ones);
         Deadline := Deadline + Milliseconds (10);
         delay until Deadline;
      end loop;
   end Reader;

end Concurrency_Example_Fixed;
