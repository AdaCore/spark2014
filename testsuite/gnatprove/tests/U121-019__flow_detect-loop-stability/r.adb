procedure R
   with SPARK_Mode => On
is
   I : Natural := 0;
   procedure Nested_Infinite_Loop_2
      with Global => (In_Out => I)
   is
       X, Z : Integer := 0;
   begin
      while X < 10 loop
         --  X is modified, so this loop will terminate
         X := X + 1;
         while Z < 5 loop
            -- But this will not
            if I > 5 then
               I := I - 1;
            end if;
         end loop;
      end loop;
   end Nested_Infinite_Loop_2;
begin
   Nested_Infinite_Loop_2;
end R;
