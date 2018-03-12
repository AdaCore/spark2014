with Bar;

procedure Test
    with SPARK_Mode => On
is
    Foo : Natural := 0;
begin
    Bar.Put ("Foo: " & Foo'Image);
    Bar.Put ("Foo: " & Foo'Img);
end Test;
