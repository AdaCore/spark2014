procedure Main
  with SPARK_Mode
is

   type T1 is delta 0.1 range 0.0 .. 1.0;
   type T2 is delta 0.1 range 1.0 .. 1.0;

   Zero   : T1 := 0.0;
   One    : T1 := 1.0;
   Result : T2 := T2 (Zero / One);

begin
   null;
end Main;
