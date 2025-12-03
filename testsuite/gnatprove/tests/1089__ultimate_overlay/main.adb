with System.Storage_Elements;
procedure Main with SPARK_Mode is
   X : Integer with Import, Address => System.Storage_Elements.To_Address (100);
   Y : Integer with Import, Address => X'Address;

   procedure P with Global => (In_Out => X) is
   begin
      Y := 12;
   end P;
begin
   null;
end Main;
