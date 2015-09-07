pragma SPARK_Mode(On);

package Initializer_Demo is

   subtype Array_Index_Type is Positive range 1 .. 10;
   type Integer_Array is array(Array_Index_Type) of Integer;

   function Add_Elements (A : Integer_Array) return Integer;

   -- Default_Value can't be applied to a subtype.
   type Accumulator is new Integer
     with Default_Value => 0;

   function Add_Elements2 (A : Integer_Array) return Integer;

   type Pair_With_Default is
      record
         X : Integer := 0;
         Y : Integer := 0;
      end record;

   function Adjust_Pair
     (P : Pair_With_Default) return Pair_With_Default;

   -- A type with partial default initialization is not allowed in SPARK.
   --
   --type Pair_With_YDefault is
   --   record
   --      X : Integer;
   --      Y : Integer := 0;
   --   end record;
   --
   --function Adjust_Pair
   --  (P : Pair_With_YDefault) return Pair_With_YDefault;

end Initializer_Demo;
