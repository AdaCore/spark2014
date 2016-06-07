package body Parent.Priv.Priv2 with
  Refined_State => (State4 => X)
is
   procedure P with Refined_Global => Parent.Priv.X is
   begin
      null;
   end P;
end Parent.Priv.Priv2;
