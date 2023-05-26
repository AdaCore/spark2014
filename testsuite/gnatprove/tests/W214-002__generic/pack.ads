package Pack is

   procedure P;

   procedure Annot
      with Annotate => (Gnatprove, Skip_Proof);

end Pack;
