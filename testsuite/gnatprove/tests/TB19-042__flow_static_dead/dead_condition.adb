procedure Dead_Condition is
   X : Integer := 0;

   procedure If_True with
     Global => null
   is
   begin
      if True then
         null;
      elsif X = 1 then
         null;
      end if;
   end If_True;

 procedure Elsif_True with
     Global => null
   is
   begin
      if False then
         null;
      elsif True then
         null;
      elsif X = 1 then
         null;
      end if;
   end Elsif_True;

begin
   null;
end Dead_Condition;
