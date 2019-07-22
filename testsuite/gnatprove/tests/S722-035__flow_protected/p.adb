package body P is
   protected body PT is
      procedure Proc is
      --  Here PT is an implicit formal parameter

         procedure Nested with Global => (Proof_In => PT) is
         --  Here it must be explicitly listed as a Global
         begin
            pragma Assert (Fun);
         end Nested;
      begin
         Nested;
      end Proc;

      function Fun return Boolean is
      begin
         return Comp;
      end Fun;
   end PT;
end P;
