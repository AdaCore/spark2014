package body Test
is

   procedure Test_01 (X : out Integer)
   is
   begin
      for I in Integer range 1 .. 10 loop
         X := 0;
         pragma Loop_Invariant (X = X'Loop_Entry);  --  uninitialized
      end loop;
   end Test_01;

end Test;
