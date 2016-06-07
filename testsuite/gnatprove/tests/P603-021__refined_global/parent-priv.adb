package body Parent.Priv with
  Refined_State => (State2 => X)
is
   procedure P with Refined_Global => X is
   begin
      null;
   end P;
end Parent.Priv;
