with Interfaces;

package Foo is
   type Bad is private
   with Annotate => (GNATprove, No_Wrap_Around);

   type Good is private;
private
   type Bad is new Interfaces.Unsigned_32;

   type Good is new Interfaces.Unsigned_32
   with Annotate => (GNATprove, No_Wrap_Around);
end Foo;
