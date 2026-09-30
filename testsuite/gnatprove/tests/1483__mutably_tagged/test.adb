pragma Extensions_Allowed (All_Extensions);

procedure Test with SPARK_Mode is
   --  Size'Class fixes the maximum in-memory size of class-wide objects,
   --  enabling stack allocation of class-wide values (mutably-tagged types).
   type Shape is tagged null record
     with Size'Class => 128;  --  class-wide objects fit in 128 bits

   type Circle is new Shape with record
      Radius : Float := 1.0;
   end record;

   --  Can now declare a class-wide variable on the stack.
   S : Shape'Class := Circle'(Radius => 2.0);
begin
   null;
end Test;
