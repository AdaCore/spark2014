package Dutch_Flag_Lib with SPARK_Mode is

   subtype Index_Type is Positive range 1 .. 100;
   subtype Color_Value is Integer range 0 .. 2;
   type Color_Array is array (Index_Type) of Color_Value;

   --  We only keep the boundaries; the array is modified in place via "in out".
   type Partition_Result is record
      Low  : Integer;
      Mid  : Integer;
      High : Integer;
   end record;

   package Permutations with Ghost is
      type Permutation is array (Index_Type) of Index_Type;
      function Is_Permutation (Map : Permutation) return Boolean is
        (for all I in Index_Type =>
           (for all J in Index_Type =>
                (if I /= J then Map (I) /= Map (J))));

      function Identity return Permutation with
        Post => (for all I in Index_Type => Identity'Result (I) = I)
        and Is_Permutation (Identity'Result);

      function Same_Values
        (Original_Array, Current_Array : Color_Array; Map : Permutation)
         return Boolean
      is
        (for all I in Index_Type =>
           Original_Array (Map (I)) = Current_Array (I))
          with Pre => Is_Permutation (Map);
   end Permutations;
   use Permutations;

   Order_Permutation : Permutation with Ghost;

   --  Expressed as a procedure, the very classic form for an in-place sort.
   procedure Flag (Values : in out Color_Array; Result : out Partition_Result)
   with
      Pre => Values'Length > 0 and then Values'Last < Natural'Last,
    Post =>
              (Result.Low <= Result.Mid
                 and then Result.Mid - 1 = Result.High) and then

              --  Logical implications expressed with "if ... then".
              (for all I in Values'Range =>
                  (if I < Result.Low then Values (I) = 0) and then
                   (if I >= Result.Low and then I < Result.Mid
                      then Values (I) = 1) and then
                     (if I >= Result.Mid then Values (I) = 2)) and then
                     Is_Permutation (Order_Permutation)
                     and then
                     Same_Values (Values'Old, Values, Order_Permutation);

end Dutch_Flag_Lib;
