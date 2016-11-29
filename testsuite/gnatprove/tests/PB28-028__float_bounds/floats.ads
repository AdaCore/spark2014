package Floats with SPARK_Mode is
   Type T_Tab_3_Float is array(1..3) of Float;
   Type T_Tab_4_L_Float is array(1..4) of Long_Float;

   Procedure Test (a : in T_Tab_3_Float; d : in out T_Tab_4_L_Float)
     with Pre => (for all i in 1..3 => a(i) in -1.0 .. 1.0);
end Floats;
