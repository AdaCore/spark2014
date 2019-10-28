package Repro
is

   type Foo_Kind is (Foo, Bar, Baz);

   subtype Bar_Kind is Foo_Kind range Bar .. Baz;

   type Blech_Type (Opt : Bar_Kind := Bar) is record
      case Opt is
         when Bar => X : Integer;
         when Baz => Y : Boolean;
      end case;
   end record;

   type Fnord_Type (Opt : Foo_Kind := Foo) is record
      case Opt is
         when Foo      => Z     : Character;
         when Bar_Kind => Blech : Blech_Type (Opt);
      end case;
   end record;

   procedure Foo;

end Repro;
