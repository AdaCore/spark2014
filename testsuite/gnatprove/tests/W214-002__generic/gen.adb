package body Gen is

   procedure Incr (X : in out T) is
   begin
      X := X + 1;
   end Incr;

   procedure Incr_Annot (X : in out T) is
   begin
      X := X + 1;
   end Incr_Annot;

end Gen;
