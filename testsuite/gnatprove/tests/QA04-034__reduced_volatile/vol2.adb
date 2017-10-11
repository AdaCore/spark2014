package body Vol2 with SPARK_Mode is
   procedure Ident (X : T; Result : out Integer) is
   begin
      Result := X.C;
   end Ident;
begin
   Ident (G(1), H1);
   Ident (G(1), H2);
   pragma Assert (H1 = H2);  --  @ASSERT:FAIL
end Vol2;
