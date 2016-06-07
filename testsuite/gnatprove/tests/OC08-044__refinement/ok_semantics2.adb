with OK_Semantics2.Priv;

package body OK_Semantics2 with
  SPARK_Mode,
  Refined_State => (State1 => X,
                    State2 => (Y, Priv.YY),
                    State3 => (Z, Priv.State))
is
   function Check return Boolean with
     Refined_Depends => (Check'Result => (X, Y, Z, Priv.YY, Priv.State))
   is
   begin
      return True;
   end Check;

   procedure Create with
     Refined_Depends => ((X, Y, Z, Priv.YY, Priv.State) => null)
   is
   begin
      null;
   end Create;

   procedure Update with
     Refined_Depends => ((X, Y, Z, Priv.YY, Priv.State) =>+ null)
   is
   begin
      null;
   end Update;

end OK_Semantics2;
