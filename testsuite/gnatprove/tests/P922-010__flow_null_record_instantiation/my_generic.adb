package body My_Generic is

   type A is array (1 .. 10) of Foo;

   Cache : A;

   procedure Assign (I : Integer;
                     X : out Foo)
   is
   begin
      X.Valid := Cache (I).Valid;
      X.Field := Cache (I).Field;
   end Assign;

end My_Generic;
