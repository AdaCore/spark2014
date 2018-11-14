with E;

procedure Foo with SPARK_Mode is
   D : constant Boolean := E;
   function C return Boolean is (D) with Ghost;

begin
   pragma Assert (True);
end;
