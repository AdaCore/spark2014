package body Refined is

   procedure P (X : in out Integer)
      with Refined_Post => (X = X'Old + 1) --@REFINED_POST:PASS
   is
   begin
      X := X + 1;
   end P;

end Refined;
