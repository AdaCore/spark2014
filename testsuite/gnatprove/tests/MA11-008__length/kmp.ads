package Kmp
with SPARK_Mode => On
is

   type A is array (Integer range <>) of Integer;

   function Init_Next (P : A) return A
   with Pre  => P'Length >= 1,
        Post => Init_Next'Result'Length = P'Length;

end Kmp;
