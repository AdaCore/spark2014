pragma SPARK_Mode (On);

with Ada.Unchecked_Conversion;

package body Unchecked is


   function B_To_A is new Ada.Unchecked_Conversion (Type_B, Type_A);


   function Convert_To_A (Var_B : in Type_B) return Type_A
   is
   begin
      return B_To_A (Var_B);
   end Convert_To_A;


end Unchecked;
