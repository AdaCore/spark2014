procedure Main with SPARK_Mode is
   procedure P1 with Always_Terminates;
   procedure P2;

   generic
   package Foo is
      function F return Boolean;
   end Foo;

   package body Foo is
      function F return Boolean is (True);
   begin
      loop
         null;
      end loop;
   end;

   procedure P1 is begin P2; end;
   procedure P2 is package My_Foo is new Foo; begin null; end;

begin
   null;
end;
