with A.Priv;

package body A with Refined_State => (State_A => (G, H, Priv.I))
is
   H : Integer;

   procedure P_1 (X : out Integer)
   is
   begin
      G := G + 1;
      X := H;
      pragma Assert (Priv.I > 0);
   end P_1;

   function F_1 return Integer is (H + Priv.F_6);

end A;
