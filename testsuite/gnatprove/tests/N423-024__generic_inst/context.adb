procedure Context (X : Integer) with
  SPARK_Mode
is
   generic
      V : Integer;
   procedure Gen with Global => (Proof_In => V);

   procedure Gen is
   begin
      pragma Assert (V > 0);
   end Gen;

   procedure Inst is new Gen (X);

   procedure Local with Global => (Proof_In => X) is
   begin
      Inst;
   end Local;
begin
   Local;
end Context;
