procedure Challenge (X, Y, Z : Float) with SPARK_Mode is
   subtype Nat is Float range 0.0 .. 2.0 ** 10;
begin
   if X in Nat and Y in Nat and Z in Nat then
      if X < Y then
         pragma Assert (X * Z <= Y * Z);
      end if;
   end if;
end Challenge;
