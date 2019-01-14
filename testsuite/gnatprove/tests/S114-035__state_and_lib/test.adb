package body Test with SPARK_Mode
is

   procedure Get (N : out Integer)
   is
      R : Integer := 0;
   begin
      N := R / 1; --  Bug is not triggered without division.
   end Get;

end Test;
