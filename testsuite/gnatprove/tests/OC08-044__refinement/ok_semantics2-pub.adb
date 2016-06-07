with OK_Semantics2.Priv;

package body OK_Semantics2.Pub with
  SPARK_Mode
is
   function Check return Boolean with
     Refined_Depends => (Check'Result => (X, Y, Z, Priv.YY, Priv.State))
   is
   begin
      return True;
   end Check;

   procedure Create is
   begin
      null;
   end Create;

   procedure Update with
     Refined_Depends => ((X, Y, Z, Priv.YY, Priv.State) =>+ null)
   is
   begin
      null;
   end Update;

end OK_Semantics2.Pub;
