with Ada.Containers.Functional_Infinite_Sequences;
with Ada.Assertions; use Ada.Assertions;
with Ada.Numerics.Big_Numbers.Big_Integers;
use ada.Numerics.Big_Numbers.Big_Integers;

with Ada.Text_IO; use Ada.Text_IO;

procedure Infinite_Sequence with SPARK_Mode is
   package Sequences is new Ada.Containers.Functional_Infinite_Sequences
     (Element_Type => Natural);
   use Sequences;

   S1 : Sequence := Empty_Sequence;

begin

   S1 := Add (S1, 1);
   pragma Assert (Get (S1, 1) = 1);

   for J in S1 loop
    --  pragma Loop_Invariant (J <= Length (S1));
      pragma Assert (Get (S1, J) = To_Integer (J));
   end loop;

end Infinite_Sequence;
