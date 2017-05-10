with P;

package body Q is

   C : constant Boolean := P.C;

   function Fun return Boolean is (C);

end;
