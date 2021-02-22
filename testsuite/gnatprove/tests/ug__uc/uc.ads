with Ada.Unchecked_Conversion;

package UC with SPARK_Mode is

   --  SPARK knows the 'Size and 'Object_Size of scalar types
   type Short_Short is range -128 .. 127;
   type U8 is mod 2 ** 8;

   --  The following representation clauses are not needed, but serve to
   --  illustrate that in the record type declaration below, U7'Size (and not
   --  U7'Object_Size) is used to check the Object_Size of the record type.
   type U7 is mod 2 ** 7
   with Size => 7,
        Object_Size => 8;

   --  Without the packing instruction, the compiler would complain that
   --  objects of type R do not fit into 8 bits.
   type R is record
      A : U7;
      B : Boolean;
   end record
   with Pack, Object_Size => 8;

   --  In both cases, the Object_Size of all involved types is 8
   function To_U8 is new Ada.Unchecked_Conversion (Source => Short_Short, Target => U8);
   function To_R is new Ada.Unchecked_Conversion (Source => U8, Target => R);
end UC;
