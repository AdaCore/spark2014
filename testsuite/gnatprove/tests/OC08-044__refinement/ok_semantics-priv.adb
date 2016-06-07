package body OK_Semantics.Priv with
  SPARK_Mode,
  Refined_State => (State => ZZ)
is
   function Check return Boolean with
     Refined_Global => (Input => (X, Y, Z, YY, ZZ))
   is
   begin
      return True;
   end Check;

   procedure Create is
   begin
      null;
   end Create;

   procedure Update with
     Refined_Global => (In_Out => (X, Y, Z, YY, ZZ))
   is
   begin
      null;
   end Update;

end OK_Semantics.Priv;
