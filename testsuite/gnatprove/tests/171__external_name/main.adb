with System.Storage_Elements;
procedure Main with SPARK_Mode is

   U : Natural with Import, Address => System.Storage_Elements.To_Address (12);
   V : Natural with Import, External_Name => "foo";
   W : Natural with Import, Link_Name => "bar";

begin
   null;
end Main;
