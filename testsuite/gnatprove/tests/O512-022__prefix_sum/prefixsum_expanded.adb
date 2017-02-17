package body PrefixSum_Expanded is pragma SPARK_Mode (On);

   procedure Upsweep (A : in out Input; Output_Space : out Positive) is
      Space : Positive := 1;
      Left  : Natural;
      Right : Natural;

      Saved_A : constant Input := A;
   begin
      while Space < A'Length loop
         pragma Loop_Invariant
            (All_Elements_In (A, Space * Maximum)
              and then
            (Space = 1 or Space = 2 or Space = 4)
              and then
            (if Space = 1 then
               (for all K in A'Range => A(K) = A'Loop_Entry (K))
             elsif Space = 2 then
               (A (1) = A'Loop_Entry (1) + A'Loop_Entry (0)
                  and then
                A (3) = A'Loop_Entry (3) + A'Loop_Entry (2)
                  and then
                A (5) = A'Loop_Entry (5) + A'Loop_Entry (4)
                  and then
                A (7) = A'Loop_Entry (7) + A'Loop_Entry (6)
                  and then
                A (0) = A'Loop_Entry (0)
                  and then
                A (2) = A'Loop_Entry (2)
                  and then
                A (4) = A'Loop_Entry (4)
                  and then
                A (6) = A'Loop_Entry (6))
             elsif Space = 4 then
               (A (3) = A'Loop_Entry (3) + A'Loop_Entry (2)
                      + A'Loop_Entry (1) + A'Loop_Entry (0)
                  and then
                A (7) = A'Loop_Entry (7) + A'Loop_Entry (6)
                      + A'Loop_Entry (5) + A'Loop_Entry (4)
                  and then
                A (1) = A'Loop_Entry (1) + A'Loop_Entry (0)
                  and then
                A (5) = A'Loop_Entry (5) + A'Loop_Entry (4)
                  and then
                A (0) = A'Loop_Entry (0)
                  and then
                A (2) = A'Loop_Entry (2)
                  and then
                A (4) = A'Loop_Entry (4)
                  and then
                A (6) = A'Loop_Entry (6))));
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

      pragma Assert
        (A (7) = Saved_A (0) + Saved_A (1) + Saved_A (2) + Saved_A (3)
               + Saved_A (4) + Saved_A (5) + Saved_A (6) + Saved_A (7)
           and then
         A (3) = Saved_A (3) + Saved_A (2) + Saved_A (1) + Saved_A (0)
           and then
         A (5) = Saved_A (5) + Saved_A (4)
           and then
         A (1) = Saved_A (1) + Saved_A (0)
           and then
         A (0) = Saved_A (0)
           and then
         A (2) = Saved_A (2)
           and then
         A (4) = Saved_A (4)
           and then
         A (6) = Saved_A (6));

      Output_Space := Space;
   end Upsweep;

   procedure Downsweep
     (Ghost : Input; A : in out Input; Input_Space : in Positive)
   is
      Space : Natural := Input_Space;
      Left  : Natural;
      Right : Natural;
      Temp  : Integer;

      Saved_A : Input;
   begin
      A (A'Last) := 0;
      Space      := Space / 2;
      Saved_A := A;
      pragma Assert
         (Saved_A (0) = Ghost(0)
            and then
          Saved_A (1) = Ghost(0) + Ghost(1)
            and then
          Saved_A (2) = Ghost(2)
            and then
          Saved_A (3) = Ghost(0) + Ghost(1) + Ghost(2) + Ghost(3)
            and then
          Saved_A (4) = Ghost(4)
            and then
          Saved_A (5) = Ghost(4) + Ghost(5)
            and then
          Saved_A (6) = Ghost(6)
            and then
          Saved_A (7) = 0);

      while Space > 0 loop
         pragma Loop_Invariant
           ((Space = 4 or Space = 2 or Space = 1)
              and then
            All_Elements_In (A, (4 / Space) * 8 * Maximum)
              and then
           (for all K in A'Range =>
              (if Space = 4 then
                 A (K) = A'Loop_Entry (K)
               elsif Space = 2 and (K = 7 or K = 3) then
                 A (7) = A'Loop_Entry (7) + A'Loop_Entry (3)
                   and then
                 A (3) = A'Loop_Entry (7)
               elsif Space = 2 then
		 A (K) = A'Loop_Entry (K)
               elsif K = 1 or K = 3 or K = 5 or K = 7 then
                   A (1) = A'Loop_Entry (7)
                     and then
                   A (3) = A'Loop_Entry (1) + A'Loop_Entry (7)
                     and then
                   A (5) = A'Loop_Entry (7) + A'Loop_Entry (3)
                     and then
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

      pragma Assert
        (A (0) = Saved_A (7)
           and then
         A (1) = Saved_A (0) + Saved_A (7)
           and then
         A (2) = Saved_A (1) + Saved_A (7)
           and then
         A (3) = Saved_A (2) + Saved_A (1) + Saved_A (7)
           and then
         A (4) = Saved_A (3) + Saved_A (7)
           and then
         A (5) = Saved_A (4) + Saved_A (3) + Saved_A (7)
           and then
         A (6) = Saved_A (3) + Saved_A (5) + Saved_A (7)
           and then
         A (7) = Saved_A (6) + Saved_A (3) + Saved_A (5) + Saved_A (7));
   end Downsweep;

end PrefixSum_Expanded;
