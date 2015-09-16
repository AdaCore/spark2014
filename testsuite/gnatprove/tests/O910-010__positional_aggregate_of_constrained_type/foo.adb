procedure Foo is
   subtype F is Float range -2.0 .. 2.0;

   type Arr is array (Natural range <>) of F;

   X : Arr := (-1.0, 1.0);
begin
   null;
end Foo;
