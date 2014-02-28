package body Foo
is

   G1 : Integer := 0;
   G2 : Integer := 0;

   type Boolean_Map is array (Boolean) of Boolean;

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

   --  Y is unused, this is OK
   function Wobble (X, Y : Integer) return Boolean is (X = 0)
   with Global  => null,
        Depends => (Wobble'Result => X,
                    null          => Y);

   procedure Test_01_Ok (A : in Integer;
                         B : in Integer;
                         R : out Boolean)
   with Global => (Input => (G1, G2)),
        Depends => (R => (A, G1),
                    null => (B, G2))
   is
   begin
      if Wibble (X => A, Y => B) then
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
      if Wibble (A, Y => B) then  --  flow error here
         R := True;
      else
         R := False;
      end if;
      B := 0;
   end Test_02_E;

   procedure Test_03_Ok (A : in Integer;
                         B : in Integer;
                         C : in Integer;
                         R : out Boolean)
   with Global => null,
        Depends => (R    => A,
                    null => (B, C))
   is
   begin
      if Wobble (A, B) then
         R := True;
      elsif Wobble (A, C) then
         R := False;
      else
         R := A = 55;
      end if;
   end Test_03_Ok;

   procedure Test_04_Ok (A : in Integer;
                         B : in Integer;
                         C : in Integer;
                         R : out Boolean)
   with Global => null,
        Depends => (R    => A,
                    null => (B, C))
   is
      Tmp : Boolean := Wobble (A, B) or Wobble (A, C);
   begin
      R := Tmp;
   end Test_04_Ok;

   procedure Test_05_Ok (A : in Integer;
                         B : in Integer;
                         R : out Boolean)
   with Global => null,
        Depends => (R    => A,
                    null => B)
   is
      Tmp : Integer := A;
   begin
      loop
         Tmp := Tmp + 1;
         exit when Wobble (Tmp, B);
      end loop;
      R := Tmp > 10;
   end Test_05_Ok;

   procedure Test_06_Ok (A : in Integer;
                         B : in Integer;
                         R : out Boolean)
   with Global => (Input => (G1, G2)),
        Depends => (R => (A, G1),
                    null => (B, G2))
   is
   begin
      R := Wibble (X => (if Wobble (A, B)
                         then A else A + 1),
                   Y => (if Wibble (A, B)
                         then A else B));
   end Test_06_Ok;

   procedure Test_07_E (A : out Integer;
                        B : out Integer;
                        R : out Boolean)
   with Global => (Output => (G1, G2))
   is
   begin
      R := Wibble (X => (if Wobble (A, B)
                         then A else A + 1),
                   Y => (if Wibble (A, B)
                         then A else B));
      A  := 0;
      B  := 0;
      G1 := 0;
      G2 := 0;
   end Test_07_E;

   procedure Test_07_Ok (A : Integer;
                         B : Integer;
                         M : in out Boolean_Map)
   with Global => null,
        Depends => (M => (A, M),
                    null => B)
   is
   begin
      M (Wobble (A, B)) := False;
   end Test_07_Ok;

   procedure Test_08_E (A : Integer;
                        M : in out Boolean_Map)
   with Global => null,
        Depends => (M => (A, M))
   is
      B : Integer;
   begin
      M (Wobble (A, B)) := False;
   end Test_08_E;

end Foo;
