with Basic; use Basic;

package body Special is

   procedure P (V : in out Sp) is
   begin
      pragma Assert (V.X = A);
      V.A_Field := 1;
   end P;

   procedure T is
      V : R := (A, 1, 0);
   begin
      pragma Assert (V.X = A);
      V.A_Field := 1;
   end T;

end Special;
