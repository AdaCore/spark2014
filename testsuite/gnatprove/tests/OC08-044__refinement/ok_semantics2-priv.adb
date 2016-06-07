package body OK_Semantics2.Priv with
  SPARK_Mode,
  Refined_State => (State => ZZ)
is
   function Check return Boolean with
     Refined_Depends => (Check'Result => (X, Y, Z, YY, ZZ))
   is
   begin
      return True;
   end Check;

   procedure Create is
   begin
      null;
   end Create;

   procedure Update with
     Refined_Depends => ((X, Y, Z, YY, ZZ) =>+ null)
   is
   begin
      null;
   end Update;

end OK_Semantics2.Priv;
