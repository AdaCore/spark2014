with Main;

package body Other
is

   type T is record
      A : Main.T;
      B : Main.T;
   end record;

   procedure Test_01 (X : in out Main.T)
   is
   begin
      X := X;
   end Test_01;

   procedure Test_02 (X : in out T)
   is
   begin
      X.A := X.B;
   end Test_02;

end Other;
