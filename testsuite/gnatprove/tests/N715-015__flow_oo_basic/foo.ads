package Foo
is

   type Root_T is tagged null record;

   function Hash (Obj : Root_T) return Natural;

   type Widget_T is new Root_T with record
      X, Y : Integer;
   end record;

   overriding function Hash (Obj : Widget_T) return Natural;

   procedure Zero_Widget (Obj : out Widget_T);

   type Nice_Widget_T is new Widget_T with record
      Round : Boolean;
   end record;

   overriding function Hash (Obj : Nice_Widget_T) return Natural;

   overriding procedure Zero_Widget (Obj : out Nice_Widget_T);

end Foo;
