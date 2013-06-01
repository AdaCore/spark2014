generic
   type Real is digits <>;

package Bar is
   type Complex is record
      Re, Im : Real'Base;
   end record;

   type Imaginary is private;

   function Im (X : Complex)   return Real'Base;
   function Im (X : Imaginary) return Real'Base;

private
   type Imaginary is new Real'Base;

end Bar;
