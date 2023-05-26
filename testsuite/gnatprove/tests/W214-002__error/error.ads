package Error is

   type T is new Integer;
   pragma Annotate (Gnatprove, Skip_Proof, T);
end Error;
