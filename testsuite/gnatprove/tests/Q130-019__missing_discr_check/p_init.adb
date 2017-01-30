package body P_Init with SPARK_Mode is

   function Init return T is
     (T'(E  => Two,
         X1 => 0,
         X2 => 0));

end P_Init;

