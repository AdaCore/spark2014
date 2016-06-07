package body Parent.Priv.Priv with
  Refined_State => (State3 => X)
is
   procedure P with Refined_Global => Parent.Priv.State2 is
   begin
      null;
   end P;
end Parent.Priv.Priv;
