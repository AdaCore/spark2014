pragma SPARK_Mode (On);

package Unchecked
is

   type Byte is mod 2 ** 8;

   subtype Byte_Array_Range is Natural range Natural'First .. Natural'Last - 1;
   type Byte_Array          is array (Byte_Array_Range range <>) of Byte;

   type Type_A is private;

   type Type_B is new Byte_Array (0 .. 3);
   for Type_B'Size use 32;


   function Convert_To_A (Var_B : in Type_B) return Type_A;


private

   type Type_A is
     record
        M_Int : Integer;
     end record;
   for Type_A'Size use 32;
   for Type_A'Alignment use 4;


end Unchecked;
