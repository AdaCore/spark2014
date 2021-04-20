procedure Test2 with SPARK_Mode Is
   I : Integer := 1;
   J : Integer := 1;
   procedure Foo with Global => null is
      package B is
         function F return Boolean;
      end B;
      package body B is
         function F return Boolean is (True);
      begin
         pragma Assert (I = 1);
         declare
            Dummy : constant Integer := J;
         begin
            null;
         end;
      end B;
   begin
      null;
   end Foo;
begin
   null;
end Test2;
