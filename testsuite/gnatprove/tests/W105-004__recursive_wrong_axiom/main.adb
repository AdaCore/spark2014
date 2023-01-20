procedure Main
  with
    SPARK_Mode => On
is

   V : Integer := 0;
   function Read_V return Integer is (V);

   --  Recursive function leading to an incorrect post axiom. The post axiom
   --  should not be available on recursive calls even if they are specialized.

   function Bad (C : Natural; F : not null access function return Integer) return Integer with
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Higher_Order_Specialization),
     Post => False;  --@POSTCONDITION:FAIL

   function Bad (C : Natural; F : not null access function return Integer) return Integer is
   begin
      if C = 0 then
         return 0;
      else
         return Bad (C - 1, Read_V'Access);
      end if;
   end Bad;

begin
   null;
end Main;
