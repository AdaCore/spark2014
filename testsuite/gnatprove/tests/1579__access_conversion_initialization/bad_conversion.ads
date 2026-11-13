with Interfaces;
with SPARK.Conversions.Access_Conversions;

package Bad_Conversion with SPARK_Mode is
   type Source is record
      Value : Interfaces.Unsigned_32;
   end record with Relaxed_Initialization, Size => 32, Alignment => 4;
   for Source use record
      Value at 0 range 0 .. 31;
   end record;
   type Positive_Word is range 1 .. 2 ** 31 - 1 with Size => 32;

   --  Instantiation must fail the initialization check in Check_Initialization,
   --  even if no conversion is called by the client.

   package Conversion is new
     SPARK.Conversions.Access_Conversions.Access_Constant_Conversions
       (Source, Interfaces.Unsigned_32);
   package Variable_Conversion is new
     SPARK.Conversions.Access_Conversions.Access_Variable_Conversions
       (Source, Interfaces.Unsigned_32);
   package Constant_Invalid_Conversion is new
     SPARK.Conversions.Access_Conversions
       .Access_Constant_Conversions_Potentially_Invalid (Source, Positive_Word);
   package Variable_Invalid_Conversion is new
     SPARK.Conversions.Access_Conversions
       .Access_Variable_Conversions_Potentially_Invalid (Source, Positive_Word);

   --  Mutable conversions also require initialized targets on return

   package Reverse_Conversion is new
     SPARK.Conversions.Access_Conversions.Access_Variable_Conversions
       (Interfaces.Unsigned_32, Source);
end Bad_Conversion;
