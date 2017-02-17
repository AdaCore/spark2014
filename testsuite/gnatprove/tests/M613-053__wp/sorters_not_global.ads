package Sorters_Not_Global
   with SPARK_Mode => On
is

   Block_Size : constant := 64;

   subtype Count_Type is Natural  range 0 .. Block_Size;
   subtype Index_Type is Positive range 1 .. Block_Size;

   type Array_Type is array (Index_Type) of Integer;

   -- Sorts the elements of the part of the array Values
   -- with indices ranging from Values'First to Limit.
   procedure Selection_Sort (Values : in out Array_Type;
                             Limit  : in Index_Type)
   with
     Depends => (Values => (Values, Limit)),
     Post    =>
       (for all J in Index_Type range Values'First .. Limit - 1 =>
          Values (J) <= Values (J + 1));

end Sorters_Not_Global;
