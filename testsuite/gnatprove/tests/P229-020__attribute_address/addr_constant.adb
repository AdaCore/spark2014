with System;                  use System;
with System.Storage_Elements; use System.Storage_Elements;

procedure Addr_Constant (V : Integer) with SPARK_Mode,
   Post => False
is

   X : constant String := "hello";
   Y : System.Address := X'Address;
begin
   null;
end Addr_Constant;
