with Ada.Text_IO; use Ada.Text_IO;
with Partition_Refinement; use Partition_Refinement;
use Partition_Refinement.Partitioning_Sets;
use Partition_Refinement.Inverse_Sets;
use Partition_Refinement.Partitions;

procedure Test_Partition_Refinement with
  SPARK_Mode => Off
is

   procedure Print_Set (A : Set) is
   begin
      Put ("A = ⟨");
      for J in A'Range loop
         Put (Index'Image(J) & " →" & Positive'Image(A(J)) & ",");
      end loop;
      Put_Line (" ⟩");
   end Print_Set;

   procedure Print_Inverse_Set (D : Inverse_Set) is
   begin
      Put ("D = ⟨");
      for C in D loop
         Put (Positive'Image(Key (D, C)) & " →" & Index'Image(Element (D, C)) & ",");
      end loop;
      Put_Line (" ⟩");
   end Print_Inverse_Set;

   function Interval_Image (I : Interval) return String is
   begin
      return "⟨ first →" & Index'Image(I.First) & ", last →" & Index'Image(I.Last) & " ⟩";
   end Interval_Image;

   procedure Print_Partition (P : Partition) is
   begin
      Put ("P = ⟨");
      for J in 0 .. Partition_Index (Length (P)) - 1 loop
         Put (Partition_Index'Image(J) & " → " & Interval_Image(Element (P, J)) & ",");
      end loop;
      Put_Line (" ⟩");
   end Print_Partition;

   procedure Print_Inverse_Partition (F : Inverse_Partition) is
   begin
      Put ("F = ⟨");
      for J in F'Range loop
         Put (Index'Image(J) & " →" & Partition_Index'Image(F(J)) & ",");
      end loop;
      Put_Line (" ⟩");
   end Print_Inverse_Partition;

   --  A is ⟨0→22,1→33,2→100,3→55,4→44,5→11⟩
   A : Set := (0 => 22, 1 => 33, 2 => 100, 3 => 55, 4 => 44, 5 => 11);

   --  F is ⟨0→0,1→0,2→0,3→1,4→1,5→1⟩
   F : Inverse_Partition := (0 => 0, 1 => 0, 2 => 0, 3 => 1, 4 => 1, 5 => 1);

   D : Inverse_Set (Capacity => 10);
   P : Partition (Capacity => 10);
   X : Partitioning_Set (Capacity => 10);

begin
   --  D is the inverse of A and is ⟨100→2,11→5,22→0,33→1,44→4,55→3⟩
   Include (D, 100, 2);
   Include (D,  11, 5);
   Include (D,  22, 0);
   Include (D,  33, 1);
   Include (D,  44, 4);
   Include (D,  55, 3);

   --  P is ⟨0→⟨first→ 0,last→ 2⟩,1→ ⟨first→ 3,last→ 5⟩⟩
   Append (P, Interval'(First => 0, Last => 2, Count => 0));
   Append (P, Interval'(First => 3, Last => 5, Count => 0));

   --  X, the input, is {11,22,44}
   Append (X, 11);
   Append (X, 22);
   Append (X, 44);

   Print_Set (A);
   Print_Inverse_Set (D);
   Print_Partition (P);
   Print_Inverse_Partition (F);

   Put_Line ("CALL REFINE");
   Refine (A, D, P, F, X);

   Print_Set (A);
   Print_Inverse_Set (D);
   Print_Partition (P);
   Print_Inverse_Partition (F);

end Test_Partition_Refinement;
