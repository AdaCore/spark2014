package body Foo.PC.C with
   SPARK_Mode,
   Refined_State => (State => B)
is
   B : Boolean := False;

   procedure Wibble (X : Boolean;
                     Y : out Boolean)
   is
   begin
      B := not B;
      Y := X xor B;
   end Wibble;

end Foo.PC.C;
