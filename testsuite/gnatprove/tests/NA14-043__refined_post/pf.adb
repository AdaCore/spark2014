package body PF
with SPARK_Mode
is
   function Prf_Public (I : Integer) return Integer
   with Refined_Post => (Prf_Public'Result = I / 2)
   is
   begin
      return I / 2;
   end Prf_Public;

   --  Same implementation as Prf_Public
   function Prf_Hidden (I : Integer) return Integer
   with Refined_Post => (Prf_Hidden'Result = I / 2)
   is
   begin
      return I / 2;
   end Prf_Hidden;

   procedure Test (A : in Integer; B : out Integer)
   with Refined_Post => (B = Prf_Public (A) and B = Prf_Hidden (A))
   is
   begin
      B := A / 2;
      pragma Assert (B = A / 2);
      pragma Assert (B = Prf_Public (A)); --  <<< This VC is discharged.
      pragma Assert (B = Prf_Hidden (A)); --  <<< This VC fails.
   end Test;

end PF;
