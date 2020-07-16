package Container
  with Elaborate_Body, Annotate => (GNATprove, Terminating)
is
   subtype My_Integer is Integer range 1 .. 200;
   subtype Small_Int is My_Integer range 1 .. 10;

   -- Custom container
   type Container is private
     with Iterable => (First       => First,
                       Has_Element => Has_Element,
                       Next        => Next,
                       Element     => Element);

   type Cursor is private;

   function First (C : Container) return Cursor;

   function Has_Element (C : Container; P : Cursor) return Boolean;

   function Next (C : Container; P : Cursor) return Cursor
     with Pre => Has_Element (C, P);

   function Element (C : Container; P : Cursor) return Integer
     with Pre => Has_Element (C, P);
   -------------------

   procedure Test4;

   X : My_Integer := 1;
   R : My_Integer := 100;
   I : Small_Int  := 1;

   B : Boolean;

private
   type Array_T is array (My_Integer) of Positive;

   type Container is record
      A : Array_T;
   end record;

   type Cursor is record
      Index : Natural;
   end record;

end Container;
