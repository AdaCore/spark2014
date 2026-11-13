with Interfaces;
with SPARK.Conversions.Access_Conversions;

package Bad_Reverse_Invalid with SPARK_Mode is
   type Target is record
      Value : Interfaces.Unsigned_32;
   end record with Relaxed_Initialization, Size => 32, Alignment => 4;
   for Target use record
      Value at 0 range 0 .. 31;
   end record;

   --  This target is rejected before Check_Reverse_Initialization: potentially
   --  invalid objects cannot have parts with relaxed initialization.

   package Conversion is new
     SPARK.Conversions.Access_Conversions
       .Access_Variable_Conversions_Potentially_Invalid
         (Interfaces.Unsigned_32, Target);
end Bad_Reverse_Invalid;
