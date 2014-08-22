package body P
is

   type T is record
      X, Y : Boolean;
   end record;
   Wibble : T;

   procedure Sel (Res : out T) is separate;
   procedure Foo is separate;

end P;
