package body Slice_Test_2
  with SPARK_Mode => On
is
   --  gnatprove gives bugbox, gcc -c fine, gcc -c -gnatc fine

   procedure Dynamic_Slice_Bound (A : in out Schedule; D : in Day)
   is
   begin
      A (Monday .. D) :=
        A (Wednesday .. Friday);
   end Dynamic_Slice_Bound;

end Slice_Test_2;
