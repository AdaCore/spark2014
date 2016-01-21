with Types; use Types;

package Update_Checks_Multidim_Unconstr is

   function Foo return AM;

   A : constant AM := Foo;
   B : constant AM := A'Update ((1, 1, 1) => 1);

end Update_Checks_Multidim_Unconstr;
