package MA16_024 is
   pragma SPARK_Mode (On);

   type T is private;

   function F return T;
private
   pragma SPARK_Mode (Off);

   type T is range 0 .. 10;

   S : T;
end MA16_024;
