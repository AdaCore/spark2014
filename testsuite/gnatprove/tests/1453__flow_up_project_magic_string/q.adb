package body Q with SPARK_Mode => On is

   --  A variable hidden in the body of another unit. Seen from P it is only
   --  known by name, so it reaches flow analysis as a magic string.

   Worker : Boolean := False;

   procedure Touch is
   begin
      Worker := not Worker;
   end Touch;

end Q;
