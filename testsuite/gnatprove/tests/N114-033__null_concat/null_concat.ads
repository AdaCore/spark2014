package Null_Concat is
   pragma SPARK_Mode (On);

   type My_Arrays is array (Integer range <>) of Integer;

   procedure P_Good;

   procedure P_Bad;
end;
