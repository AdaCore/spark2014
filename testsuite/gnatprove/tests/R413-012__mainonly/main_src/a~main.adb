with A; use A;

package body A.Main
is

   procedure P (Y :    out T)
   is
      X : T;
   begin
      Set (X);
      Y := X / 2;
   end P;

end A.Main;
