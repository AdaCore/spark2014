procedure Test_Loop with SPARK_Mode is
   X : array (Integer range 1 .. 100) of aliased Integer := (others => 0);
   C : Integer := 0;
begin
   for I in 1 .. 100 loop
      declare
         Y : aliased Integer with Import, Address => X (I)'Address;
      begin
         pragma Loop_Invariant (if I > 1 then Y = C); --  This should not be proved, as Y designates another part of the array at each iteration
         C := Y;
      end;
   end loop;
end;
