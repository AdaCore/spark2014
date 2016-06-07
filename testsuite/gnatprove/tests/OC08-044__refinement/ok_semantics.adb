with OK_Semantics.Priv;

package body OK_Semantics with
  SPARK_Mode,
  Refined_State => (State1 => X,
                    State2 => (Y, Priv.YY),
                    State3 => (Z, Priv.State))
is
   function Check return Boolean with
     Refined_Global => (Input => (X, Y, Z, Priv.YY, Priv.State))
   is
   begin
      return True;
   end Check;

   procedure Create with
     Refined_Global => (Output => (X, Y, Z, Priv.YY, Priv.State))
   is
   begin
      null;
   end Create;

   procedure Update with
     Refined_Global => (In_Out => (X, Y, Z, Priv.YY, Priv.State))
   is
   begin
      null;
   end Update;

end OK_Semantics;
