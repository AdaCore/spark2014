separate (Pkg)
package body Pack is

   package Sub is
      procedure P (X : in out Integer);
   end Sub;

   procedure P (X : in out Integer) is
   begin
      X := X + 1;
      Sub.P (X);
   end P;

   package body Sub is separate;

end Pack;
