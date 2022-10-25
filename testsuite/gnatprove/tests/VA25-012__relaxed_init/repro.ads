package Repro
is
   type Foo_Type is array (1 .. 42) of Boolean;

   type Item_Type is
   record
      A : Boolean;
      B : Foo_Type;
      C : Foo_Type;
   end record;

   procedure Update (Item : out Item_Type);
end Repro;
