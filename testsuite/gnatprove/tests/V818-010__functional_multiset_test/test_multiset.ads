with Natural_Multisets;
with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;

package test_multiset with SPARK_Mode => On is
   use Natural_Multisets;

   procedure Test_Basic_Operations with SPARK_Mode => On;

   procedure Test_Basic_Properties with SPARK_Mode => On;

   procedure Test_Properties with
     SPARK_Mode => On;

   procedure Test_Basic_Constructors with SPARK_Mode => On;

   procedure Test_Operations with SPARK_Mode => On;

end test_multiset;
