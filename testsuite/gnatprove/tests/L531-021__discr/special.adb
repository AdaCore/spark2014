with Basic; use Basic;

package body Special is

   procedure P (V : in out Sp) is
   begin
      pragma Assert (V.X = A);
      V.A_Field := 1;
      --  discriminant check fails here
      V.C_Field1 := True;
   end P;

   -- specialize on assignment (in subprogram body)
   procedure T is
      V : R := (A, 1, 0);
   begin
      pragma Assert (V.X = A);
      V.A_Field := 1;
      --  discriminant check fails here
      V.C_Field1 := True;
   end T;

end Special;
