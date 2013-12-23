package body Refined is

   procedure P (X : in out Integer)
      with Refined_Post => (X = X'Old + 1)
   is
   begin
      X := X + 1;
   end P;

end Refined;
