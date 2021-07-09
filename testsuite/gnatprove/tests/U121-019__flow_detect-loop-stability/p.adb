procedure P
   with SPARK_Mode => On
is
   I : Natural := 0;
   procedure Infinite_Loop
      with Global => (In_Out => I)
   is
       X : Integer := 0;
   begin
      while X < 10 loop
         -- We want to be able to detect that X is 'stable' in the loop, i.e.
         -- it does not change over iterations, and so this is an infinite
         -- loop. Currently this detection is not supported.
         if I > 10 then
            I := I - 1;
         end if;
      end loop;
   end Infinite_Loop;
begin
   Infinite_Loop;
end P;
