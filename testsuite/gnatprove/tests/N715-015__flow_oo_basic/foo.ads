package Foo
is

   type Root_T is tagged null record;

   function Hash (Obj : Root_T) return Natural;

   type Widget_T is new Root_T with record
      X, Y : Integer;
   end record;

   function Hash (Obj : Widget_T) return Natural;

end Foo;
