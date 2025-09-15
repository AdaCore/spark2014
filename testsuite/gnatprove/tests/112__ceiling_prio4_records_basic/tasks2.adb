with Proxy;

package body Tasks2 is

   task body TTA1 is
   begin
      loop
         Proxy.Proxy_Proc1;
      end loop;
   end;

   task body TTA2 is
   begin
      loop
         Proxy.Proxy_Proc2;
      end loop;
   end;

   task body TTB1 is
   begin
      loop
         Proxy.Proxy_Proc1;
      end loop;
   end;

   task body TTB2 is
   begin
      loop
         Proxy.Proxy_Proc2;
      end loop;
   end;

end Tasks2;
