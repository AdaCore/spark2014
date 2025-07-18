procedure Float_Test with SPARK_Mode is
   type Foo is range 0 .. 4;
   X : Float := 3.14159265359;
   F : Foo;
begin
   F := Foo (X + X);
end;
