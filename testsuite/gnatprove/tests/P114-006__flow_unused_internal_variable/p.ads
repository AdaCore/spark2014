package P is

   type T is new Integer with Predicate => Foo;

   function Foo return Boolean;

end;
