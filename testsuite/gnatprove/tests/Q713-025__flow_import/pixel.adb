with System.Storage_Elements; use System.Storage_Elements;

function Pixel (Buffer : System.Address; Offset : Natural) return Integer with SPARK_Mode => Off is
   Value : aliased Integer with
      Import, Address => Buffer + Storage_Offset (Offset);

   function Proxy return Integer with
      Import, Address => Buffer - Storage_Offset (Offset);

begin
   return Value + Proxy;
end Pixel;
