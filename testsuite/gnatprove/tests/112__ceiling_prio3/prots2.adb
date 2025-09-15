with Proxy;

package body Prots2 is

   procedure P_Local is
   begin
      PO.PP1;
   end;

   protected body PO is
      procedure PP1 is
      begin
         Proxy.Proc1;
         Proxy.Proc2;
         Proxy.Proc3;
      end;

      procedure PP2 is
      begin
         PP1;  -- Direct self call;
      end;

      procedure PP3 is
      begin
         P_Local;  -- Indirect self call;
      end;
   end;

end Prots2;
