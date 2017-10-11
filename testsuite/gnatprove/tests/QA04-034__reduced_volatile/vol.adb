package body Vol with SPARK_Mode is
   function Ident (X : T) return Integer is
   begin
      return X.C;
   end Ident;
   H3 : constant Integer := Ident (G(1));
begin
   H1 := Ident (G(1));
   H2 := Ident (G(1));
   pragma Assert (H1 = H2);  --  @ASSERT:FAIL
end Vol;
