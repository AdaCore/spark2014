with System.Storage_Elements; use System.Storage_Elements;
with System; use System;

procedure Main2 with SPARK_Mode is
   type My_Offs is new Storage_Offset;
   Addr : Address := To_Address (16#8000_0000#);
   Off  : My_Offs :=  Addr mod My_Offs (-1); --@PRECONDITION:FAIL
begin
   null;
end Main2;
