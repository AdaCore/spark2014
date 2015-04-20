package body Nested_Problem is
   --  Preconditions to stop inlining...
   procedure Level_1 (N : in out Integer)
   is
      procedure Level_2 (X : in out Integer)
      with Pre => True
      is
         procedure Level_3
         with Pre => True
         is
         begin
            X := X + 1;
            Level_2 (X);
         end Level_3;
      begin
         if X <= 100 then
            Level_3;
         end if;
      end Level_2;
   begin
      Level_2 (N);
   end Level_1;
end Nested_Problem;
