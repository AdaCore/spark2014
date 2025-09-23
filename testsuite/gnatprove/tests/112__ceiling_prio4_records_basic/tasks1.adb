with Proxy;

package body Tasks1 is

   task body TA1 is
   begin
      loop
         Proxy.Proxy_Proc1;
      end loop;
   end;

   task body TA2 is
   begin
      loop
         Proxy.Proxy_Proc2;
      end loop;
   end;

   task body TB1 is
   begin
      loop
         Proxy.Proxy_Proc1;
      end loop;
   end;

   task body TB2 is
   begin
      loop
         Proxy.Proxy_Proc2;
      end loop;
   end;

end Tasks1;
