procedure Test_Swap_Lines with SPARK_Mode is
   type Matrix is array (Positive range <>, Positive range <>) of Natural;

   procedure Swap_Lines (M : in out Matrix; L1, L2 : Positive) is
      Tmp : Natural;
   begin
      for C in M'Range (2) loop
         pragma Loop_Invariant (for all I in M'First (2) .. C - 1 =>
                                  M (L1, I) = M'Loop_Entry (L2, I)
                                and M (L2, I) = M'Loop_Entry (L1, I));
         Tmp := M (L1, C);
         M (L1, C) := M (L2, C);
         M (L2, C) := Tmp;
      end loop;
   end Swap_Lines;

   procedure Swap_Lines_2 (M : in out Matrix; L1, L2 : Positive) is
      Tmp : Natural;
   begin
      for C in M'First (2) - 1 .. M'Last (2) - 1 loop
         pragma Loop_Invariant (for all I in M'First (2) .. C =>
                                  M (L1, I) = M'Loop_Entry (L2, I)
                                and M (L2, I) = M'Loop_Entry (L1, I));
         pragma Loop_Invariant (for all I in C + 1 .. M'Last (2) =>
                                  M (L1, I) = M'Loop_Entry (L1, I)
                                and M (L2, I) = M'Loop_Entry (L2, I));
         Tmp := M (L1, C + 1);
         M (L1, C + 1) := M (L2, C + 1);
         M (L2, C + 1) := Tmp;
      end loop;
   end Swap_Lines_2;

   procedure Incr_Diag (M : in out Matrix) is
   begin
      for I in M'Range (1) loop
         pragma Loop_Invariant (for all K in M'First (1) .. I - 1 =>
                                  M (K, K) = M'Loop_Entry (K, K) + 1);
         pragma Loop_Invariant (for all K in M'First (1) .. I - 1 =>
                                  (for all H in M'First (1) .. I - 1 =>
                                       (if K /= H then
                                             M (K, H) = M'Loop_Entry (K, H))));
         M (I, I) := M (I, I) + 1;
      end loop;
   end Incr_Diag;

   M : Matrix (1 .. 10, 1 .. 10);
begin
   M := (5      => (others => 1),
         7      => (others => 2),
         others => (others => 0));
   Swap_Lines (M, 5, 7);
   pragma Assert (for all I in 1 .. 10 =>
                    (for all J in 1 .. 10 =>
                       (if I = 5 then M (I, J) = 2
                        elsif I = 7 then M (I, J) = 1
                        else M (I, J) = 0)));
   M := (5      => (others => 1),
         7      => (others => 2),
         others => (others => 0));
   Swap_Lines_2 (M, 5, 7);
   pragma Assert (for all I in 1 .. 10 =>
                    (for all J in 1 .. 10 =>
                       (if I = 5 then M (I, J) = 2
                        elsif I = 7 then M (I, J) = 1
                        else M (I, J) = 0)));
   M := (others => (others => 0));
   Incr_Diag (M);
   pragma Assert (for all I in 1 .. 10 =>
                    (for all J in 1 .. 10 =>
                       (if I = J then M (I, J) = 1
                        else M (I, J) = 0)));
end Test_Swap_Lines;
