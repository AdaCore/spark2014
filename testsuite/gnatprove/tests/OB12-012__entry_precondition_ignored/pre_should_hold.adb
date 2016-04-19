package body Pre_Should_Hold is
   protected body Prot_Int is
      function Is_Positive return Boolean is (The_Int > 0);

      entry Increase when Condition is
      begin
         pragma Assert (Is_Positive);
         if The_Int /= Integer'Last then
            The_Int := The_Int + 1;
         end if;
      end Increase;
   end Prot_Int;
end Pre_Should_Hold;
