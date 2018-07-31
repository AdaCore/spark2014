package Types with SPARK_Mode is

   type T is mod 2 ** 32;
   pragma Provide_Shift_Operators(T);
end Types;
