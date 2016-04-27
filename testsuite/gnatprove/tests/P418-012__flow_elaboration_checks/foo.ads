--  This package requires Elaborate_Body for various reasons
package Foo is
   type T is record
      A : Boolean;
      B : Boolean;
   end record;

   type U is private;

   Body_Elaborated : Boolean := True;
   Foo             : T       := (False, True);
   Bar             : Boolean := False;

   procedure P;

private
   type U is new Integer;
   Baz : U := 0;
end Foo;
