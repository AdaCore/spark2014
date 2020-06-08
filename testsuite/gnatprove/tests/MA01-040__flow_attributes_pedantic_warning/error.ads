package Error
is
   type R is record
      F1 : Integer;
   end record;

   function Alignment_Of (X : in R) return Natural;

end Error;
