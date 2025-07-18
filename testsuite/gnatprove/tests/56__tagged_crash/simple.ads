package Simple is

   type Inner is tagged null record;

   type Any_Inner is access Inner;

   type Outer is record
      Z : Any_Inner;
   end record;

   procedure Foo (X : in out Outer);
   procedure Bar (Y : in out Inner);

end Simple;
