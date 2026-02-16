procedure Main with SPARK_Mode is
   V  : Integer := 12;
   C1 : constant Integer := V;
   C2 : constant Integer with Import, Address => C1'Address;

   function F return Integer is (C2) with Global => C2;

begin
   null;
end Main;
