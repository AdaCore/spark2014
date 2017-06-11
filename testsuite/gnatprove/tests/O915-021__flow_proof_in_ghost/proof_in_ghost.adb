procedure Proof_In_Ghost with
  SPARK_Mode
is
   B : Boolean := True;
   G : Boolean with Ghost;

   procedure Sub with
     Global => (Proof_In => B, Output => G)
   is
      Tmp : Boolean := B with Ghost;
   begin
      G := B;
      pragma Assert (B);
      pragma Assert (Tmp);
   end Sub;

begin
   Sub;
end Proof_In_Ghost;
