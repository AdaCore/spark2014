procedure Challenge2 (X, Y, Z : Float) with SPARK_Mode is
   subtype Nat is Float range 0.0 .. 2.0 ** 10;
begin
   if X in Nat'Range and Y in Nat'Range and Z in Nat'Range then
      if X < Y then
         pragma Assert (X * Z <= Y * Z);
      end if;
   end if;
end Challenge2;
