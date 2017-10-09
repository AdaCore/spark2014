package body Vol with SPARK_Mode is
   function Ident (X : T) return Integer is
   begin
      return X.C;
   end Ident;
begin
   H := Ident (G);
end Vol;
