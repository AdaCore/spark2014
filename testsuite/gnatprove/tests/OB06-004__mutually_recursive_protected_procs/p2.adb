with P1;

package body P2 with
  Refined_State => (State => PO)
is

   function Prio return Integer is (5);

   protected PO is
      pragma Priority (Prio);
      procedure Dummy; --@CEILING_PRIORITY_PROTOCOL:FAIL
   end;

   protected body PO is
      procedure Dummy is
      begin
         P1.Proxy;
      end;
   end;

   procedure Proxy is
   begin
      PO.Dummy;
   end;

end;
