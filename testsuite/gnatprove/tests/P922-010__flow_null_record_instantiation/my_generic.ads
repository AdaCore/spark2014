generic
   type T is private;
package My_Generic is

   type Foo is record
      Valid : Boolean;
      Field : T;
   end record;

   procedure Assign (I : Integer;
                     X : out Foo);

end My_Generic;
