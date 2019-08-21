with Foo; use Foo;

procedure Bar (A, B : Unbounded_String) with SPARK_Mode is
begin
   pragma Assert
     (String'(To_String (A) & To_String (B)) (1 .. Length (A))
      = To_String (A));
end Bar;
