package Lib is

   type T_Integer_32 is range -2 ** 31 .. 2 ** 31 - 1
     with Size => 32;

   subtype T_Natural_32  is T_Integer_32 range 0 .. T_Integer_32'Last;
   subtype T_Positive_32 is T_Integer_32 range 1 .. T_Integer_32'Last;


   type T_OBIT is new Integer;

end Lib;
