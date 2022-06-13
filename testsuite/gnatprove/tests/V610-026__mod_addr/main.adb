with System.Storage_Elements; use System.Storage_Elements;
with System; use System;

procedure Main with SPARK_Mode is
   Addr : Address := To_Address (16#8000_0000#);
   Off  : Storage_Offset :=  Addr mod Storage_Offset (-1); --@PRECONDITION:FAIL
begin
   null;
end Main;
