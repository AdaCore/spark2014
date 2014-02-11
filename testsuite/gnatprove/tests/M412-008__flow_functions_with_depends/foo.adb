package body Foo
is

   G1 : Integer := 0;
   G2 : Integer := 0;

   function Wibble (X, Y : Integer) return Boolean
     with Global => (Input    => G1,
                     Proof_In => G2),
          Depends => (Wibble'Result => (X, G1),
                      null          => Y),
          Pre => (Y = G2)
   is
   begin
      pragma Assert (Y = G2);
      return X = G1;
   end Wibble;

   procedure Test_01_Ok (A : in Integer;
                         B : in Integer;
                         R : out Boolean)
   with Global => (Input => (G1, G2)),
        Depends => (R => (A, G1),
                    null => (B, G2))
   is
   begin
      if Wibble (A, B) then
         R := True;
      else
         R := False;
      end if;
   end Test_01_Ok;

   procedure Test_02_E (A : in Integer;
                        B : out Integer;
                        R : out Boolean)
   with Global => (Input => (G1, G2)),
        Depends => (R    => (A, G1),
                    B    => null,
                    null => G2)
   is
   begin
      if Wibble (A, B) then  --  flow error here
         R := True;
      else
         R := False;
      end if;
      B := 0;
   end Test_02_E;

end Foo;
