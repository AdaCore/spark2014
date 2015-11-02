package body PO_T8 is

   protected body P_Int is
      function Get return Integer is (The_Protected_Int);

      procedure Allow_Increase is
      begin
         Condition := True;
      end Allow_Increase;

      entry Increase when Condition is
      begin
         if The_Protected_Int = Integer'Last then
            The_Protected_Int := Integer'First;
         else
            The_Protected_Int := The_Protected_Int + 1;
         end if;
         Condition := False;
      end Increase;
   end P_Int;

   task body T is
      The_Last_Of_The_Integers : Integer := Integer'Last;
   begin
      loop
         pragma Loop_Invariant (The_Last_Of_The_Integers >= P_Int.Get);
         P_Int.Allow_Increase;
         P_Int.Increase;
      end loop;
   end T;
end PO_T8;
