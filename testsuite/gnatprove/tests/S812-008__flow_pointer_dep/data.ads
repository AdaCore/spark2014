package Data is
   type AI is access Integer;
   type AAI is access AI;
   procedure Copy_Pointer (A : in AAI; B : out AI) with
      Global  => null,
      Depends => (B => A, A => A);
end Data;
