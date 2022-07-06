with Ada.Containers.Functional_Infinite_Sequences;
with Ada.Numerics.Big_Numbers.Big_Integers;
use ada.Numerics.Big_Numbers.Big_Integers;

procedure Infinite_Sequence with SPARK_Mode is
   package Sequences is new Ada.Containers.Functional_Infinite_Sequences
     (Element_Type => Natural);
   use Sequences;

   S1 : Sequence := Empty_Sequence;
   S2 : Sequence := Empty_Sequence;

begin

   --  Make sure the Sequences are actually Empty

   pragma Assert (Length (S1) = 0);
   pragma Assert (Length (S2) = 0);

   --  Build two sequences :
   --
   --  S1 : [1, 2, 3]
   --  S2 : [1, 2, 3, 4, 5]

   for J in 1 .. 3 loop
      S1 := Add (S1, J);
   end loop;
   S2 := S1;
   for J in 4 .. 5 loop
      S2 := Add (S2, J);
   end loop;

   pragma Assert (Length (S1) = 3);
   pragma Assert (Length (S2) = 5);

   for J in S1 loop
      pragma Assert (Get (S1, J) = To_Integer (J));
   end loop;

   for J in S2 loop
      pragma Assert (Get (S2, J) = To_Integer (J));
   end loop;

   --  Test "<"

   pragma Assert (S1 < S2);
   pragma Assert (not (S2 < S1));

   --  Test "<="

   pragma Assert (S1 <= S1);
   pragma Assert (S1 <= S2);
   pragma Assert (not (S2 <= S1));

   --  Test Contains

   pragma Assert (Contains (S1, 2, 3, 2));
   pragma Assert (not Contains (S1, 2, 3, 1));

   --  Test Equal Except

   declare
      S3 : Sequence;

   begin
      S3 := S1;
      S3 := Set (S3, 2, 3);

      --  S1 : [1, 2, 3]
      --  S3 : [1, 3, 3]

      pragma Assert (Equal_Except (S1, S3, 2));
      pragma Assert (not Equal_Except (S1, S2, 3));
   end;

   declare
      S3 : Sequence := S2;

   begin
      S3 := Set (S3, 1, 6);
      S3 := Set (S3, 2, 6);

      --  S2 : [1, 2, 3, 4, 5]
      --  S3 : [6, 6, 3, 4, 5]

      pragma Assert (Equal_Except (S2, S3, 1, 2));
      pragma Assert (not Equal_Except (S2, S3, 1, 4));
   end;

   --  S1 : [1, 2, 3]
   --  S2 : [1, 2, 3, 4, 5]

   declare
      S3 : Sequence;
      S4 : Sequence;

   begin

      --  Test Add

      S4 := Add (S1, 1, 0);
      --  S4 : [0, 1, 2, 3]

      for J in S4 loop
         if (J = 1) then
            pragma Assert (Get (S4, J) = 0);
         else
            pragma Assert (Get (S4, J) = To_Integer (J) - 1);
         end if;
      end loop;

      S2 := Add (S1, 4);

      --  S2 :  [1, 2, 3, 4]

      for J in S2 loop
         pragma Assert (Get (S2, J) = To_Integer (J));
      end loop;

      --  Test Set

      S3 := Set (S2, 1, 4);
      S3 := Set (S3, 4, 3);

      --  S3 : [4, 2, 3, 5]

      pragma Assert (Get (S3, 1) = 4);
      pragma Assert (get (S3, 2) = 2);
      pragma Assert (Get (S3, 3) = 3);
      pragma Assert (Get (S3, 4) = 3);

      --  S1 : [1, 2, 3]
      --  S2 : [1, 2, 3, 4]
      --  S3 : [4, 2, 3, 3]
      --  S4 : [0, 1, 2, 3]

      --  Test Range_Equal

      pragma Assert (Range_Equal (S2, S3, 2, 3));
      pragma Assert (not Range_Equal (S3, S4, 2, 3));

      --  Test Range_Shifted

      pragma Assert (Range_Shifted (S2, S4, 1, 3, 1));
      pragma Assert (Range_Shifted (S4, S3, 3, 3, -1));
      pragma Assert (not Range_Shifted (S2, S3, 2, 3, 1));

      --  Test Constant_Range

      pragma Assert (Constant_Range (S3, 3, 4, 3));
      pragma Assert (not Constant_Range (S3, 2, 3, 2));
   end;

   --  S1 : [1, 2, 3]
   --  S2 : [1, 2, 3, 4]

   -- Test Remove and =

   pragma Assert (not (S1 = S2));

   S2 := Remove (S2, 4);

   pragma Assert (S1 = S2);

   S2 := Set (S2, 1, 0);

   pragma Assert (not (S1 = S2));

   S1 := Remove (S1, 2);

   pragma Assert (Get (S1, 1) = 1);
   pragma Assert (Get (S1, 2) = 3);


end Infinite_Sequence;
