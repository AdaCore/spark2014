procedure P (M : Integer)
is
   PM : Integer renames M;

   function F return Integer
   is
   begin
      return PM;
   end F;
begin
   null;
end P;
