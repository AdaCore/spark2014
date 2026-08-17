pragma SPARK_Mode (On);

procedure Nearby is
   G : Integer := 1;
   K : constant Integer := G;

   generic
      C : Integer;
   procedure Copy (R : out Integer);

   procedure Copy (R : out Integer) is
   begin
      R := C;
   end Copy;

   procedure Copy_Literal (R : out Integer) with Global => null is
      procedure Instance is new Copy (C => 42);
   begin
      Instance (R);
   end Copy_Literal;

   procedure Copy_Constant (R : out Integer) with Global => K is
      procedure Instance is new Copy (C => K);
   begin
      Instance (R);
   end Copy_Constant;

   generic
      V : in out Integer;
   procedure Increment;

   procedure Increment is
   begin
      V := V + 1;
   end Increment;

   procedure Increment_Global with Global => (In_Out => G) is
      procedure Instance is new Increment (V => G);
   begin
      Instance;
   end Increment_Global;

   procedure Increment_Again with Global => (In_Out => G) is
      procedure Instance is new Increment (V => G);
   begin
      Instance;
   end Increment_Again;

   procedure Increment_Third with Global => (In_Out => G) is
      procedure Instance is new Increment (V => G);
   begin
      Instance;
   end Increment_Third;

   R : Integer;
begin
   Copy_Literal (R);
   Copy_Constant (R);
   Increment_Global;
   Increment_Again;
   Increment_Third;
end Nearby;
