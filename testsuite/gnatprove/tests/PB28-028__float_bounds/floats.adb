package body Floats with SPARK_Mode is
   Procedure Test (a : in T_Tab_3_Float; d : in out T_Tab_4_L_Float) is
   begin
      pragma assert (A(1) in -1.0..1.0);
      pragma assert (A(2) in -1.0..1.0);
      pragma assert (A(3) in -1.0..1.0);

      d(1) := 1.0;
      d(2) := Long_Float (a(1)*0.5);
      d(3) := Long_Float (a(2)*0.5);
      d(4) := Long_Float (a(3)*0.5);

      pragma assert (d(1) in -1.0..1.0);
      pragma assert (d(2) in -1.0..1.0);
      pragma assert (d(3) in -1.0..1.0);
      pragma assert (d(4) in -1.0..1.0);
      pragma assert (for all i in 1..4 => d(i) in -1.0 .. 1.0);
   end Test;
end Floats;
