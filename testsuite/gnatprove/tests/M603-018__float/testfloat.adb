procedure Testfloat is
   Max_Float : constant Float := Float'Last;
   Max_Double : constant Long_Float := Long_Float'Last;
   X : Float := 0.0;
   Y : Float := 1.0;
   Z : Float := 0.5;
   T : Float := (X + Y) / 2.0;

   type T1 is new Float;

   procedure Triplet (X, Y, Z : Float) with
     Pre => Z in X .. Y
       and then X in -10.0 .. 10.0
       and then Y = X + 1.0
       and then Float'Floor (Z) = X
       and then Float'Ceiling (Z) = Y;

   procedure Triplet (X, Y, Z : Float) is
      T : Float := (X + Y) / 2.0;
   begin
      pragma Assert (Float'Floor (X) = X);
      pragma Assert (Float'Floor (Y) = Y);
      pragma Assert (Float'Floor (Z) = X);
      pragma Assert (Float'Floor (T) = X);

      pragma Assert (Float'Ceiling (X) = X);
      pragma Assert (Float'Ceiling (Y) = Y);
      pragma Assert (Float'Ceiling (Z) = Y);
      pragma Assert (Float'Ceiling (T) = Y);

      pragma Assert (Z in X .. Y);
      pragma Assert (T in X .. Y);
   end Triplet;

begin
   pragma Assert (Float'Floor (X) = X);
   pragma Assert (Float'Floor (Y) = Y);
   pragma Assert (Float'Floor (Z) = X);
   pragma Assert (Float'Floor (T) = X);

   pragma Assert (Float'Ceiling (X) = X);
   pragma Assert (Float'Ceiling (Y) = Y);
   pragma Assert (Float'Ceiling (Z) = Y);
   pragma Assert (Float'Ceiling (T) = Y);

   pragma Assert (Z in X .. Y);
   pragma Assert (T in X .. Y);

   Triplet (X, Y, Z);
   Triplet (X, Y, T);
end Testfloat;
