with Interfaces;

package Relaxed_UC with SPARK_Mode is
   subtype Word is Interfaces.Unsigned_32;

   type Byte is record
      Value : Interfaces.Unsigned_8;
   end record with Relaxed_Initialization, Size => 8;
   for Byte use record
      Value at 0 range 0 .. 7;
   end record;

   type Bytes is array (4 .. 7) of Byte
     with Component_Size => 8, Alignment => 4;

   procedure Precise with Global => null;
   procedure Imprecise with Global => null;
   procedure Partial_Source (X : Bytes; Result : out Word)
     with Global => null;
   procedure Object_Relaxed_Source (Result : out Word)
     with Global => null;
end Relaxed_UC;
