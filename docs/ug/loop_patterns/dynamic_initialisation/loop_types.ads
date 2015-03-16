package Loop_Types
  with SPARK_Mode
is
   Max_Seq_Length : constant Natural := 1000;

   subtype Index_T is Natural range 1 .. Max_Seq_Length;

   subtype Component_T is Positive;

   type Arr_T is array (Index_T range <>) of Component_T;

end Loop_Types;
