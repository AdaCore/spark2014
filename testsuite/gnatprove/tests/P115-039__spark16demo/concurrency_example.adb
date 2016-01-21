with Ada.Real_Time; use Ada.Real_Time;
with Ada.Text_IO;

package body Concurrency_Example is

   task body Writer is
      Flip     : Boolean := True;
      Deadline : Time    := Clock;
   begin
      loop
         if Flip then
            Data := All_Ones;
         else
            Data := All_Zeroes;
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
         Value := Data;
         --  do some work with value read
         Ada.Text_IO.Put_Line (if Value = All_Zeroes then "all zeroes"
                               elsif Value = All_Ones then "all ones"
                               else "data race detected");
         pragma Assert (Value = All_Zeroes or Value = All_Ones);
         Deadline := Deadline + Milliseconds (10);
         delay until Deadline;
      end loop;
   end Reader;

end Concurrency_Example;
