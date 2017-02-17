package body Sgs is

   function A (X: T) return Float is (C (X));

   procedure F (X1 : T; X2 : T; X3 : T; X4 : T) is
      R1 : Float;
      R2 : U;
   begin
      pragma Assert (A (X1) >= 0.0);
      pragma Assert (A (X1) <= 14.0);

      pragma Assert (A (X2) <= 14.0);
      pragma Assert (A (X2) >= 0.0);

      pragma Assert (A (X3) >= 0.0 and then A (X3) <= 14.0);

      R1 := A (X4);
      R2 := A (X4);
      pragma Assert (R1 >= 0.0);
      pragma Assert (R1 <= 14.0);
      pragma Assert (R2 >= 0.0);
      pragma Assert (R2 <= 14.0);
   end F;

end Sgs;
