pragma SPARK_Mode(On);

package Utility is
   pragma Assertion_Policy(Pre => Check, Post => Ignore);

   subtype Index_Type is Natural range 0 .. 1023;
   type Integer_Array is array(Index_Type) of Integer;

   function Search_For_Zero (Values : Integer_Array) return Index_Type
     with
       Pre => (for some Index in Index_Type => Values (Index) = 0),
       Post => Values (Search_For_Zero'Result) = 0;

end Utility;
