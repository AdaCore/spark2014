with System; use System;
with System.Address_To_Access_Conversions;

procedure Main with SPARK_Mode is
   package Int_ATAC is new System.Address_To_Access_Conversions (Integer);
   use Int_ATAC;
   Addr : Address with Import;
   C1 : constant Object_Pointer := To_Pointer (Addr);
begin
   Addr := To_Address (C1); -- Rejected
end Main;
