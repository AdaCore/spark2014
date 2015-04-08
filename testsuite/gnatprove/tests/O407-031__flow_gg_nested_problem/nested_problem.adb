package body Nested_Problem is
   procedure P (X : in out Integer) is
      procedure Increase_And_Recurse
        with Pre => True  --  Contract prevents inlining
      is
      begin
         X := X + 1;
         P (X);
      end Increase_And_Recurse;
   begin
      if X <= 100 then
         Increase_And_Recurse;
      end if;
   end P;
end Nested_Problem;
