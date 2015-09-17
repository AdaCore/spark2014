package Search_Array with SPARK_Mode is

   type N_Array is array (Positive range <>) of Natural;

   function Search_Zero_P (A : N_Array) return Positive;

   function Search_Zero_N (A : N_Array) return Natural;

end Search_Array;
