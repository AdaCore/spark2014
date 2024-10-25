procedure P1 is
   package P is
      type T is private
         with Default_Initial_Condition => null;
   private
      type T is null record;
   end P;

   X : access P.T := new P.T;
begin
   null;
end;
