pragma SPARK_Mode(On);

package Various is

   subtype Index_Type is Positive range 1 .. 10;
   type Integer_Array is array(Index_Type) of Integer;

   function Search_For_Zero(Values : Integer_Array) return Index_Type
     with
       Pre => (for some I in Values'Range => (Values(I) = 0));

   procedure Silly;

end Various;
