package Gen is

   generic
      type T is range <>;
   procedure Incr (X : in out T) with Pre => True;

   generic
      type T is range <>;
   procedure Incr_Annot (X : in out T)
      with Pre => True,
           Annotate => (Gnatprove, Skip_Proof);
end Gen;
