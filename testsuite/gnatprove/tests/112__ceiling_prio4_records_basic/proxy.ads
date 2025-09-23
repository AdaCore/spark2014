package Proxy is

   procedure Proxy_Proc1;
   --  Priority of the caller must be <= 3
   procedure Proxy_Proc2;
   --  Priority of the caller must be <= 3

end Proxy;
