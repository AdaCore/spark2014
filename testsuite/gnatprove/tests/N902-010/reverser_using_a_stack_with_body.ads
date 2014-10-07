with A_Stack_No_SPARK_Contracts_With_Body;
use A_Stack_No_SPARK_Contracts_With_Body;
package Reverser_Using_A_Stack_With_Body with
  SPARK_Mode
is
   subtype Array_Range is Natural range 1 .. 10000;
   type Array_Of_Items is array (Array_Range range <>) of Item;

   procedure Reverse_Array (A : in out Array_Of_Items) with
     Pre => A'Length > 0 and then A'Length <= Stack_Size;

end Reverser_Using_A_Stack_With_Body;
