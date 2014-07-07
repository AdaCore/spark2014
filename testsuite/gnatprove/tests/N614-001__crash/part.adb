with Ada.Text_IO; use Ada.Text_IO;

package body Part
with SPARK_Mode
is

   procedure Swap (X : in out Set; A, B : Positive)
     with Pre => A in X'Range and B in X'Range,
     Post =>
     (X (A) = X'Old (B) and then X (B) = X'Old (A) and then
          (for all I in X'Range =>
               (if I /= A and then I /= B then X (I) = X'Old (I))));

   procedure Split_Partition (A : in out Set;
                              X : Set;
                              Result : in out Partition;
                              Part_Count : in out Natural);

   ----------
   -- Swap --
   ----------

   procedure Swap (X : in out Set; A, B : Positive) is
      Tmp : Integer := X (A);
   begin
      X (A) := X (B);
      X (B) := Tmp;
   end Swap;


   procedure Split_Partition (A : in out Set;
                              X : Set;
                              Result : in out Partition;
                              Part_Count : in out Natural) is
      First : Positive := A'First;
      Last  : Positive := A'Last;
   begin
      while First <= Last loop
         if Mem (X, A (First)) then
            First := First + 1;
         else
            Swap (A, First, Last);
            Last := Last - 1;
         end if;
         pragma Loop_Invariant (Same_Set (A'Loop_Entry, A));
      end loop;
      Part_Count := Part_Count + 1;
      Result (Part_Count) := A'First;
      if First = A'First or else Last = A'Last then
         null;
      else
         Part_Count := Part_Count + 1;
         Result (Part_Count) := First;
      end if;
   end Split_Partition;

   ------------
   -- Refine --
   ------------

   procedure Refine
     (A        : in out Set;
      P        : Partition;
      X        : Set;
      NP       : out Partition;
      Num_Part : out Natural) is

      Last_Index : Positive := A'First;
   begin
      Num_Part := 0;
      for PI in P'Range loop
         Split_Partition (A (Last_Index .. P (PI) - 1),
                          X,
                          NP,
                          Num_Part);
         Last_Index := P (PI);

      end loop;
      Split_Partition (A (Last_Index .. A'Last), X, NP, Num_Part);
   end Refine;

end Part;
