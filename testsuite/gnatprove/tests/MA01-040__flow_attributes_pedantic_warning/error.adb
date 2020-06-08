package body Error
is

   function Alignment_Of (X : in R) return Natural
   is
   begin
      return X'Alignment;
   end Alignment_Of;

end Error;
