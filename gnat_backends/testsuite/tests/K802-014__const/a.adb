procedure A is
begin

   Test_Block:
   declare

      TC_Max_Loop_Count        : constant Natural := 1000;

      procedure Check_Discrete_Values is
      begin
         for i in 1..TC_Max_Loop_Count loop
            null;
         end loop;
      end Check_Discrete_Values;
   begin

      null;

   end Test_Block;

end A;
