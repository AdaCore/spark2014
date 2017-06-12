with P2;

package body P1 with
  Refined_State => (State => PO)
is

   function Prio return Integer is (5);

   protected PO is
      pragma Priority (Prio);
      procedure Dummy with
        Global => (In_Out => P2.State);
   end;

   protected body PO is
      procedure Dummy is
      begin
         P2.Proxy;
      end;
   end;

   procedure Proxy is
   begin
      PO.Dummy;
   end;

end;
