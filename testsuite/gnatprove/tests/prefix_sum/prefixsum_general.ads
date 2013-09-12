with Types; use Types;

package PrefixSum_General is pragma SPARK_Mode (On); 

   Tree_Depth : constant := 3;
   Maximum    : constant := Integer'Last / (Index'Last + 1);

   function Is_Even (K : Integer) return Boolean is (K mod 2 = 0);

   function Summation (A : Input; Start_Pos, End_Pos : Index) return Integer
   with
     Pre => Start_Pos <= End_Pos;

   function Summation (A : Input; Start_Pos, End_Pos : Index) return Integer is
      (if Start_Pos = End_Pos then A (Start_Pos)
       else A (End_Pos) + Summation (A, Start_Pos, End_Pos - 1));

   procedure Upsweep (A : in out Input; Output_Space : out Positive) with
     Pre  => (for all K in A'Range => A (K) in -Maximum .. Maximum),
     Post => (for all K in A'Range => (if Is_Even (K) then A (K) = A'Old (K)))
       and then A (A'Last) = Summation (A'Old, 0, A'Last);

   procedure Downsweep
     (Ghost : Input; A : in out Input; Input_Space : in Positive);

end PrefixSum_General;
