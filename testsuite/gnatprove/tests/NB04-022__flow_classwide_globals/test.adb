with Foo; use Foo;

package body Test is

   procedure Test_01 (X  : Base_T'Class;
                      O1 : out Boolean;
                      O2 : out Boolean)
   with Post => O1 = O2
   is
   begin
      G2 := False;
      O1 := X.F;
      G2 := True;
      O2 := X.F;
   end Test_01;

end Test;
