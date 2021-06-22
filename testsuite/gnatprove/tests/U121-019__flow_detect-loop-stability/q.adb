procedure Q
   with SPARK_Mode => On
is
   I : Natural := 0;
   procedure Nested_Infinite_Loop
      with Global => (In_Out => I)
   is
       X, Z : Integer := 0;
   begin
      while X < 10 loop
         -- We want to be able to detect that X is 'stable' in the loop, i.e.
         -- it does not change over iterations, and so this is an infinite
         -- loop. Currently this detection is not supported.
         if I > 10 then
            I := I - 1;
         end if;
         while Z < 5 loop
            --  Same with Z
            if I > 5 then
               I := I - 1;
            end if;
         end loop;
      end loop;
   end Nested_Infinite_Loop;
begin
   Nested_Infinite_Loop;
end Q;
