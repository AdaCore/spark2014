package body Conversion_Fixed is

   procedure Test (X : T; X2 : T2; X3 : T3; X4 : T4) is
      Y  : T;
      Y2 : T2;
      Y3 : T3;
      Y4 : T4;
   begin
      Y := T(X4);
      pragma Assert (if X4 = -10.0 then Y = -10.0);
      pragma Assert (if X4 = 2.0 then Y = 2.0);
      pragma Assert (if X4 = 4.0 then Y = 4.0);

      Y2 := T2(X3);
      pragma Assert (if X3 = -10.0 then Y2 = -10.0);
      pragma Assert (if X3 = 2.0 then Y2 = 2.0);
      pragma Assert (if X3 = 4.0 then Y2 = 4.0);

      Y3 := T3(X2);
      pragma Assert (if X2 = -10.0 then Y3 = -10.0);
      pragma Assert (if X2 = 2.0 then Y3 = 2.0);
      pragma Assert (if X2 = 4.0 then Y3 = 4.0);

      Y3 := T3(X4);
      pragma Assert (if X4 = -10.0 then Y3 = -10.0);
      pragma Assert (if X4 = 2.0 then Y3 = 2.0);
      pragma Assert (if X4 = 4.0 then Y3 = 4.0);

      Y4 := T4(X);
      pragma Assert (if X = -10.0 then Y4 = -10.0);
      pragma Assert (if X = 2.0 then Y4 = 2.0);
      pragma Assert (if X = 4.0 then Y4 = 4.0);

      Y4 := T4(X3);
      pragma Assert (if X3 = -10.0 then Y4 = -10.0);
      pragma Assert (if X3 = 2.0 then Y4 = 2.0);
      pragma Assert (if X3 = 4.0 then Y4 = 4.0);
   end Test;

end Conversion_Fixed;
