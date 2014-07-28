package Printable is

   type Object is interface;

   procedure Print (This : Object) is abstract;

end Printable;
