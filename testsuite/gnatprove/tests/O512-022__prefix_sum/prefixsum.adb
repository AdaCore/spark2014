package body PrefixSum is pragma SPARK_Mode (On);

   procedure Upsweep (A : in out Input; Output_Space : out Positive) is
      Space : Positive := 1;
      Left  : Natural;
      Right : Natural;
   begin
      while Space < A'Length loop
         pragma Loop_Invariant
            (All_Elements_In (A, Space * Maximum)
              and then
            (Space = 1 or Space = 2 or Space = 4)
              and then
            (for all K in A'Range =>
              (if (K + 1) mod 8 = 0
                 and then Space = 8
               then
                 A (K) = A'Loop_Entry (0) + A'Loop_Entry (1) +
                         A'Loop_Entry (2) + A'Loop_Entry (3) +
                         A'Loop_Entry (4) + A'Loop_Entry (5) +
                         A'Loop_Entry (6) + A'Loop_Entry (7)
               elsif (K + 1) mod 4 = 0
                 and then Space >= 4
               then
                 A (K) = A'Loop_Entry (K) + A'Loop_Entry (K-1) +
                         A'Loop_Entry (K-2) + A'Loop_Entry (K-3)
               elsif (K + 1) mod 2 = 0
                 and then Space >= 2
               then
                 A (K) = A'Loop_Entry (K) + A'Loop_Entry (K-1)
               else
                 A (K) = A'Loop_Entry (K))));
         pragma Loop_Variant (Increases => Space);

         Left := Space - 1;

         while Left < A'Length loop
            pragma Loop_Invariant (
              (Left + 1) mod Space = 0
                and then
              All_Left_Elements_In (A, Left, Space * 2 * Maximum)
                and then
              All_Right_Elements_In (A, Left - 1, Space * Maximum)
                and then
              (Left + 1) mod (Space * 2) = Space
                and then
              (if Left >= A'Length then Left = 8 or Left = 9)
                and then
              (for all K in A'Range =>
                (if K in A'First .. Left - Space
                   and then (K + 1) mod (2 * Space) = 0
                 then
                    A (K) = A'Loop_Entry (K) + A'Loop_Entry (K - Space)
                 else
                    A (K) = A'Loop_Entry (K))));
            pragma Loop_Variant (Increases => Left);

            Right     := Left + Space;
            A (Right) := A (Left) + A (Right);
            Left      := Left + Space * 2;
         end loop;
         Space := Space * 2;
      end loop;
      Output_Space := Space;
   end Upsweep;

   procedure Downsweep
     (Ghost : Input; A : in out Input; Input_Space : in Positive)
   is
      Space : Natural := Input_Space;
      Left  : Natural;
      Right : Natural;
      Temp  : Integer;
   begin
      A (A'Last) := 0;
      Space      := Space / 2;

      while Space > 0 loop
         pragma Loop_Invariant
           ((Space = 4 or Space = 2 or Space = 1)
              and then
            All_Elements_In (A, (4 / Space) * 8 * Maximum)
              and then
            (for all K in A'Range =>
              	 (if Space = 4 then
                    A (K) = A'Loop_Entry (K)
                 elsif Space = 2 and then (K+1) mod 8 = 0 then
                    A (K) = A'Loop_Entry (K) + A'Loop_Entry (K - 2*Space)
                 elsif Space = 2 and then (K+1) mod 4 = 0 then
                    A (K) = A'Loop_Entry (K + 2*Space)
                 elsif Space = 2 then
                    A (K) = A'Loop_Entry (K)
                 elsif Space = 1 and then (K+1) mod 2 = 0 then
                    A (1) = A'Loop_Entry (7) and
                    A (3) = A'Loop_Entry (1) + A'Loop_Entry (7) and
                    A (5) = A'Loop_Entry (7) + A'Loop_Entry (3) and
                    A (7) = A'Loop_Entry (5) + A'Loop_Entry (7)
                          + A'Loop_Entry (3)
                 else
                    A (K) = A'Loop_Entry (K))));
         pragma Loop_Variant (Decreases => Space);

         Right := Space * 2 - 1;
         while Right < A'Length loop
            pragma Loop_Invariant (
              (for all K in A'Range =>
                (if K in A'First .. Right - Space * 2 then
                  (if (K + 1) mod (2 * Space) = 0 then
                      A (K) = A'Loop_Entry (K) + A'Loop_Entry (K - Space)
                   elsif (K + 1) mod Space = 0 then
                      A (K) = A'Loop_Entry (K + Space)
                   else
                   A (K) = A'Loop_Entry (K))
                 else
                   A (K) = A'Loop_Entry (K)))
                 and then
              (Right + 1) mod (Space * 2) = 0
                 and then
              (if Right >= A'Length then
                 Right = 9 or Right = 11 or Right = 15));
            pragma Loop_Variant (Increases => Right);

            Left      := Right - Space;
            Temp      := A (Right);
            A (Right) := A (Left) + A (Right);
            A (Left)  := Temp;
            Right     := Right + Space * 2;
         end loop;
         Space := Space / 2;
      end loop;
   end Downsweep;

end PrefixSum;
