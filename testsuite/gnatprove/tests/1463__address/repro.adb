with System;                  use System;
with System.Storage_Elements; use System.Storage_Elements;

procedure Repro with SPARK_Mode is

   A : constant := 16#4021_0000#;

   function Probe return Address is
     (To_Address (A) + Storage_Offset (4));

   B : Address := Probe;

begin
   pragma Unreferenced (B);
end Repro;
