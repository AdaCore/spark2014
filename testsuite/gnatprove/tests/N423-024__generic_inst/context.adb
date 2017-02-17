procedure Context (X : Integer) with
  SPARK_Mode
is
   generic
      V : Integer;
   procedure Gen;

   procedure Gen is
   begin
      pragma Assert (V > 0);
   end Gen;

   procedure Inst is new Gen (X);

   procedure Local is
   begin
      Inst;
   end Local;
begin
   Local;
end Context;
