package body Infoflow is pragma SPARK_Mode (On);
   procedure Machine_Step is
   begin
      declare
         Data_0_V1, Data_1_V1 : Character;
      begin
         if In_0_Rdy_V1 and not Out_1_Rdy_V1 then
            Data_0_V1    := In_0_Dat_V1;
            In_0_Rdy_V1  := False;
            Out_1_Dat_V1 := Data_0_V1;
            Out_1_Rdy_V1 := True;
         end if;
         if In_1_Rdy_V1 and not Out_0_Rdy_V1 then
            Data_1_V1    := In_1_Dat_V1;
            In_1_Rdy_V1  := False;
            Out_0_Dat_V1 := Data_1_V1;
            Out_0_Rdy_V1 := True;
         end if;
      end;

      --  duplicate version 2

      declare
         Data_0_V2, Data_1_V2 : Character;
      begin
         if In_0_Rdy_V2 and not Out_1_Rdy_V2 then
            Data_0_V2    := In_0_Dat_V2;
            In_0_Rdy_V2  := False;
            Out_1_Dat_V2 := Data_0_V2;
            Out_1_Rdy_V2 := True;
         end if;
         if In_1_Rdy_V2 and not Out_0_Rdy_V2 then
            Data_1_V2    := In_1_Dat_V2;
            In_1_Rdy_V2  := False;
            Out_0_Dat_V2 := Data_1_V2;
            Out_0_Rdy_V2 := True;
         end if;
      end;
   end Machine_Step;

   procedure SinglePositionAssign (Flag : in Int; Value : in FlagValue) is
   begin
      Flags (Flag) := Value;
   end SinglePositionAssign;

   procedure SinglePositionAssign
     (Flag_V1, Flag_V2 : in Int; Value_V1, Value_V2 : in FlagValue) is
   begin
      Flags_V1 (Flag_V1) := Value_V1;

      --  duplicate version 2

      Flags_V2 (Flag_V2) := Value_V2;
   end SinglePositionAssign;

   procedure ScrubCache (Cache_V1, Cache_V2 : out SensorCacheType) is
   begin
      for I in SensorIds loop
         Cache_V1 (I) := 0;
         pragma Loop_Invariant (for all K in SensorIds =>
                                  (if K <= I then Cache_V1 (K) = 0));
      end loop;

      --  duplicate version 2

      for I in SensorIds loop
         Cache_V2 (I) := 0;
         pragma Loop_Invariant (for all K in SensorIds =>
                                  (if K <= I then Cache_V2 (K) = 0));
      end loop;
   end ScrubCache;

   procedure CopyKeys
     (InKeys_V1, InKeys_V2   : in KeyTableType;
      OutKeys_V1, OutKeys_V2 : out KeyTableType;
      J                      : in KeyTableEntries) is
   begin
      for I in KeyTableEntries loop
         OutKeys_V1 (I) := InKeys_V1 (I);
         pragma Loop_Invariant (for all K in KeyTableEntries =>
                              (if K <= I then OutKeys_V1 (K) = InKeys_V1 (K)));
      end loop;

      --  duplicate version 2

      for I in KeyTableEntries loop
         OutKeys_V2 (I) := InKeys_V2 (I);
         pragma Loop_Invariant (for all K in KeyTableEntries =>
                              (if K <= I then OutKeys_V2 (K) = InKeys_V2 (K)));
      end loop;
   end CopyKeys;

   procedure FlipHalves (H_V1, H_V2 : in out H_Type; I : Integer) is
   begin
      declare
         T_V1 : Content;
         M_V1 : Integer;
      begin
         M_V1 := H_V1'Last / 2;
         for Q_V1 in H_V1'First .. M_V1 loop
            pragma Loop_Invariant (for all K in H_V1'Range =>
                             (if K < Q_V1 then
                                 H_V1 (K) = H_V1'Loop_Entry (K + M_V1)
                              elsif K > Q_V1 + M_V1 then
                                 H_V1 (K) = H_V1'Loop_Entry (K - M_V1)
                              else H_V1 (K) = H_V1'Loop_Entry (K)));
            T_V1 := H_V1 (Q_V1);
            H_V1 (Q_V1) := H_V1 (Q_V1 + M_V1);
            H_V1 (Q_V1 + M_V1) := T_V1;
         end loop;
      end;

      pragma Assert_And_Cut (True);

      --  duplicate version 2

      declare
         T_V2 : Content;
         M_V2 : Integer;
      begin
         M_V2 := H_V2'Last / 2;
         for Q_V2 in H_V2'First .. M_V2 loop
            pragma Loop_Invariant (for all K in H_V2'Range =>
                             (if K < Q_V2 then
                                 H_V2 (K) = H_V2'Loop_Entry (K + M_V2)
                              elsif K > Q_V2 + M_V2 then
                                 H_V2 (K) = H_V2'Loop_Entry (K - M_V2)
                              else H_V2 (K) = H_V2'Loop_Entry (K)));
            T_V2 := H_V2 (Q_V2);
            H_V2 (Q_V2) := H_V2 (Q_V2 + M_V2);
            H_V2 (Q_V2 + M_V2) := T_V2;
         end loop;
      end;
   end FlipHalves;

   procedure FlipHalves2 (H_V1, H_V2 : in out H_Type; I : Integer) is
      procedure Flip (H : in out H_Type) with
        Pre  => H'First = 1 and H'Last >= 1,
        Post => (for all K in H'Range =>
                   (if K <= H'Last/2 then H (K) = H'Old (K + H'Last/2)
                    else H (K) = H'Old (K - H'Last/2)));

      procedure Flip (H : in out H_Type) is
         T : Content;
         M : Integer;
      begin
         M := H'Last / 2;
         for Q in H'First .. M loop
            pragma Loop_Invariant (for all K in H'Range =>
                             (if K < Q then H (K) = H'Loop_Entry (K + M)
                              elsif K > Q + M then
                                 H (K) = H'Loop_Entry (K - M)
                              else H (K) = H'Loop_Entry (K)));
            T         := H (Q);
            H (Q)     := H (Q + M);
            H (Q + M) := T;
         end loop;
      end Flip;

   begin
      Flip (H_V1);
      --  duplicate version 2
      Flip (H_V2);
   end FlipHalves2;

   procedure ArrayPartitionedTransfer
     (A_V1, A_V2 : out Arr;
      B_V1, C_V1, B_V2, C_V2 : in Arr;
      K_1, K_2, I : Integer) is
   begin
      for I_V1 in A_V1'First .. K_1 loop
         pragma Loop_Invariant (for all M in A_V1'First .. I_V1-1 =>
                          A_V1 (M) = B_V1 (M));
         A_V1 (I_V1) := B_V1 (I_V1);
      end loop;

      pragma Assert_And_Cut
        (for all M in A_V1'First .. K_1 =>
           A_V1 (M) = B_V1 (M));

      for I_V1 in K_1+1 .. A_V1'Last loop
         pragma Loop_Invariant ((for all M in A_V1'First .. K_1 =>
                                   A_V1 (M) = B_V1 (M))
                                  and then
                                (for all M in K_1+1 .. I_V1-1 =>
                                   A_V1 (M) = C_V1 (M - K_1)));
         A_V1 (I_V1) := C_V1 (I_V1 - K_1);
      end loop;

      pragma Assert_And_Cut
        ((for all M in A_V1'First .. K_1 =>
            A_V1 (M) = B_V1 (M))
               and then
         (for all M in K_1+1 .. A_V1'Last =>
            A_V1 (M) = C_V1 (M - K_1)));

      --  duplicate version 2

      for I_V2 in A_V2'First .. K_2 loop
         pragma Loop_Invariant (for all M in A_V2'First .. I_V2-1 =>
                          A_V2 (M) = B_V2 (M));
         A_V2 (I_V2) := B_V2 (I_V2);
      end loop;

      pragma Assert_And_Cut
        ((for all M in A_V1'First .. K_1 =>
            A_V1 (M) = B_V1 (M))
               and then
         (for all M in K_1+1 .. A_V1'Last =>
            A_V1 (M) = C_V1 (M - K_1))
               and then
         (for all M in A_V2'First .. K_2 =>
            A_V2 (M) = B_V2 (M)));

      for I_V2 in K_2+1 .. A_V2'Last loop
         pragma Loop_Invariant ((for all M in A_V2'First .. K_2 =>
                                   A_V2 (M) = B_V2 (M))
                                  and then
                                (for all M in K_2+1 .. I_V2-1 =>
                                   A_V2 (M) = C_V2 (M - K_2)));
         A_V2 (I_V2) := C_V2 (I_V2 - K_2);
      end loop;
   end ArrayPartitionedTransfer;
end Infoflow;
