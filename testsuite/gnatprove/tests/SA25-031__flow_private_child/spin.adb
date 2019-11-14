with sPIN.Tunnel;

package body sPIN
with
   Refined_State => (Internal_State => Tunnel.Tunnel_Internal,
                     External_State => Tunnel.Tunnel_External)
is

   function State_Invariant (S : State_Type) return Boolean
   is (S.Current = Tunnel.Is_Valid);

   ----------------------------------------------------------------------------

   procedure Initialize
      (State : out State_Type)
   is
   begin
      State.Current := False;
   end Initialize;

   ----------------------------------------------------------------------------

   procedure Display
      (State : in out State_Type)
   is
   begin
      pragma Unreferenced (State);
   end Display;

end sPIN;
