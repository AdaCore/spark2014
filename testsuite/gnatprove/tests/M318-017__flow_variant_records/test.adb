package body Test
is

   type DT is (Foo, Bar, Baz);

   type Wibble (D : DT) is record
      Flag : Boolean;
      case D is
         when Foo =>
            X : Integer;
         when Bar =>
            Y : Boolean;
         when Baz =>
            Z : DT;
      end case;
   end record;

   procedure Test_Init_01 (X : Integer;
                           R : out Wibble)
   is
   begin
      if X > 0 then
         R := (D    => Foo,
               X    => X,
               Flag => False);
         --  Missing Flag here would be illegal.
      else
         R := (D    => Baz,
               Z    => Bar,
               Flag => False);
      end if;
   end Test_Init_01;

   procedure Test_Init_02 (R : out Wibble)
   is
      V : Wibble (Baz);
   begin
      V.Flag := True;
      --  Error - we have not initialised V.Z

      R := V;
   end Test_Init_02;

   procedure Test_Init_03 (R : out Wibble)
   is
      V : Wibble (Baz);
   begin
      V.Flag := True;
      V.Z    := Foo;

      R := V;
   end Test_Init_03;

end Test;
