package body Foo
is

   G1 : Integer := 0;
   G2 : Integer := 0;

   function Wibble (X, Y : Integer) return Boolean
     with Global => (Input    => G1,
                     Proof_In => G2),
          Depends => (Wibble'Result => (X, G1),
                      null          => Y)
   is
   begin
      pragma Assert (Y = G2);
      return X = G1;
   end Wibble;

end Foo;
