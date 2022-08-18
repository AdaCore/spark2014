with SPARK.Containers.Functional.Multisets;
with Ada.Containers; use Ada.Containers;

with Ada.Text_IO; use Ada.Text_IO;
with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;

--  with My_Multiset; use My_Multiset;

with SPARK.Containers.Functional.Sets;

with test_multiset;
use test_multiset;

procedure Test with SPARK_Mode => On is
begin
   Test_Basic_Operations;

   Test_Basic_Properties;

   Test_Properties;

   Test_Basic_Constructors;

   Test_Operations;
end Test;

