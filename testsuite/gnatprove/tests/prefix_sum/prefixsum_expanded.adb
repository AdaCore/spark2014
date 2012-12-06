with Ada.Text_IO; use Ada.Text_IO;
package body PrefixSum_Expanded is

   procedure Upsweep (A : in out Input; Output_Space : out Positive) is
      Space : Positive := 1;
      Left  : Natural;
      Right : Natural;
      Copy1 : Input;
      Copy2 : Input;
   begin
      Copy1 := A;
      while Space < A'Length loop
         pragma Loop_Invariant
            (All_Elements_In (A, Space * Maximum)
              and then
            (Space = 1 or Space = 2 or Space = 4)
              and then
            (if Space = 1 then
               (for all K in A'Range => A(K) = Copy1(K))
             elsif Space = 2 then
                (A(1) = Copy1(1) + Copy1(0) and A(3) = Copy1(3) + Copy1(2) and
                 A(5) = Copy1(5) + Copy1(4) and A(7) = Copy1(7) + Copy1(6) and
                 A(0) = Copy1(0) and A(2) = Copy1(2) and A(4) = Copy1(4) and A(6) = Copy1(6))
            elsif Space = 4 then
                (A(3) = Copy1(3) + Copy1(2) + Copy1(1) + Copy1(0) and A(7) = Copy1(7) + Copy1(6) + Copy1(5) + Copy1(4) and
                 A(1) = Copy1(1) + Copy1(0) and A(5) = Copy1(5) + Copy1(4) and
                 A(0) = Copy1(0) and A(2) = Copy1(2) and A(4) = Copy1(4) and A(6) = Copy1(6))));
         pragma Loop_Variant (Increases => Space);

         Left := Space - 1;

         Copy2 := A;
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
                    A (K) = Copy2 (K) + Copy2 (K - Space)
                 else
                    A (K) = Copy2 (K))));
            pragma Loop_Variant (Increases => Left);

            Right     := Left + Space;
            A (Right) := A (Left) + A (Right);
            Left      := Left + Space * 2;
         end loop;
         Space := Space * 2;
      end loop;
      pragma Assert
       (A (7) = Copy1 (0) + Copy1 (1) + Copy1 (2) + Copy1 (3) + Copy1 (4) + Copy1 (5) + Copy1 (6) + Copy1 (7) and
        A (3) = Copy1 (3) + Copy1 (2) + Copy1 (1) + Copy1 (0) and
        A (5) = Copy1 (5) + Copy1(4) and A (1) = Copy1 (1) + Copy1(0) and
        A (0) = Copy1 (0) and A (2) = Copy1 (2) and A (4) = Copy1 (4) and A (6) = Copy1 (6));
      Output_Space := Space;
   end Upsweep;

   procedure Downsweep
     (Ghost : Input; A : in out Input; Input_Space : in Positive)
   is
      Space : Natural := Input_Space;
      Left  : Natural;
      Right : Natural;
      Temp  : Integer;
      Copy1 : Input;
      Copy2 : Input;
   begin
      A (A'Last) := 0;
      Space      := Space / 2;
      Copy1 := A;
      pragma Assert
         (Copy1(0) = Ghost(0)
          and Copy1(1) = Ghost(0) + Ghost(1)
          and Copy1(2) = Ghost(2)
          and Copy1(3) = Ghost(0) + Ghost(1) + Ghost(2) + Ghost(3)
          and Copy1(4) = Ghost(4)
          and Copy1(5) = Ghost(4) + Ghost(5)
          and Copy1(6) = Ghost(6)
          and Copy1(7) = 0);
      while Space > 0 loop
         pragma Loop_Invariant
           ((Space = 4 or Space = 2 or Space = 1)
              and then
            All_Elements_In (A, (4 / Space) * 8 * Maximum)
              and then
           (for all K in A'Range =>
              (if Space = 4 then
                 A(K) = Copy1(K)
               elsif Space = 2 and (K = 7 or K = 3)  then
               	 A(7) = Copy1(7) +Copy1(3) and A(3) = Copy1(7)
               elsif Space = 2 then
		 A(K) = Copy1(K)
               elsif (K = 1 or K = 3 or K = 5 or K = 7) then
                 A(1) = Copy1(7) and
                 A(3) = Copy1(1) + Copy1(7) and
                 A(5) = Copy1(7) + Copy1(3) and
                 A(7) = Copy1(5) + Copy1(7) + Copy1(3)
               else
                 A(K) = Copy1(K))));
         pragma Loop_Variant (Decreases => Space);

         Right := Space * 2 - 1;
         Copy2 := A;
         while Right < A'Length loop
            pragma Loop_Invariant (
              (for all K in A'Range =>
                (if K in A'First .. Right - Space * 2 then
                  (if (K + 1) mod (2 * Space) = 0 then
                      A (K) = Copy2 (K) + Copy2 (K - Space)
                   elsif (K + 1) mod Space = 0 then
                      A (K) = Copy2 (K + Space)
                   else
                   A (K) = Copy2 (K))
                 else
                   A (K) = Copy2 (K)))
                 and then
              (Right + 1) mod (Space * 2) = 0
                 and then
              (if Right >= A'Length then
                 Right = 9 or Right = 11 or Right = 15));
            pragma Loop_Variant (Increases => Right);

            Left      := Right - Space;
            Temp      := A (Right);
            A (Right) := A (Left) + A(Right);
            A (Left)  := Temp;
            Right     := Right + Space * 2;
         end loop;
         Space := Space / 2;
      end loop;
      pragma Assert
        ((A(0) = Copy1(7)
          and A(1) = Copy1(0) + Copy1(7)
          and A(2) = Copy1(1) + Copy1(7)
          and A(3) = Copy1(2) + Copy1(1) + Copy1(7)
          and A(4) = Copy1(3) + Copy1(7)
          and A(5) = Copy1(4) + Copy1(3) + Copy1(7)
          and A(6) = Copy1(3) + Copy1(5) + Copy1(7)
          and A(7) = Copy1(6) + Copy1(3) + Copy1(5) + Copy1(7)));
   end Downsweep;

end PrefixSum_Expanded;
