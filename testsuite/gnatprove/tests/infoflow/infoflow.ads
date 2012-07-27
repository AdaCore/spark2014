package Infoflow is
   In_0_Rdy_V1, In_1_Rdy_V1, Out_0_Rdy_V1, Out_1_Rdy_V1 : Boolean;
   In_0_Dat_V1, In_1_Dat_V1, Out_0_Dat_V1, Out_1_Dat_V1 : Character;

   In_0_Rdy_V2, In_1_Rdy_V2, Out_0_Rdy_V2, Out_1_Rdy_V2 : Boolean;
   In_0_Dat_V2, In_1_Dat_V2, Out_0_Dat_V2, Out_1_Dat_V2 : Character;

   procedure Machine_Step with
     Contract_Case => (Name     => "Out_0_Dat from In_1_Dat",
                       Mode     => Nominal,
                       Requires => In_1_Dat_V1 = In_1_Dat_V2 and
                                   (In_1_Rdy_V1 and not Out_0_Rdy_V1) and
                                   (In_1_Rdy_V2 and not Out_0_Rdy_V2),
                       Ensures  => Out_0_Dat_V1 = Out_0_Dat_V2),
     Contract_Case => (Name     => "Out_0_Dat from itself",
                       Mode     => Nominal,
                       Requires => Out_0_Dat_V1 = Out_0_Dat_V2 and
                                   (not In_1_Rdy_V1 or Out_0_Rdy_V1) and
                                   (not In_1_Rdy_V2 or Out_0_Rdy_V2),
                       Ensures  => Out_0_Dat_V1 = Out_0_Dat_V2);

   --  Types and variables for SinglePositionAssign

   type Int is range 1 .. 10;
   type FlagValue is (F0, F1, F2, F3, F4);
   type FlagArray is array (Int) of FlagValue;

   Flags, Flags_V1, Flags_V2 : FlagArray;

   --  Checking global annotation of SinglePositionAssign

   procedure SinglePositionAssign (Flag : in Int; Value : in FlagValue) with
     Post => (for all K in Int =>
                (if K /= Flag then Flags (K) = Flags'Old (K)));

   --  Checking derives annotation of SinglePositionAssign

   procedure SinglePositionAssign
     (Flag_V1, Flag_V2 : in Int; Value_V1, Value_V2 : in FlagValue)
   with
     Contract_Case => (Name     => "Flags(Flag) from Value",
                       Mode     => Nominal,
                       Requires => Value_V1 = Value_V2,
                       Ensures  => Flags_V1(Flag_V1) = Flags_V2(Flag_V2));

   --  Types and variables for ScrubCache

   type SensorIds is range 1 .. 10;
   type SensorCacheType is array (SensorIds) of Integer;

   --  Checking derives annotation of ScrubCache

   procedure ScrubCache (Cache_V1, Cache_V2 : out SensorCacheType) with
     Contract_Case => (Name     => "Cache(J) from null",
                       Mode     => Nominal,
                       Requires => True,
                       Ensures  => (for all K in SensorIds =>
                                      Cache_V1 (K) = Cache_V2 (K)));

   --  Types and variables for CopyKeys

   type KeyTableEntries is range 1 .. 10;
   type KeyTableType is array (KeyTableEntries) of Integer;

   --  Checking derives annotation of CopyKeys

   procedure CopyKeys
     (InKeys_V1, InKeys_V2   : in KeyTableType;
      OutKeys_V1, OutKeys_V2 : out KeyTableType;
      J                      : in KeyTableEntries)
   with
     Contract_Case => (Name     => "OutKeys(J) from InKeys(J)",
                       Mode     => Nominal,
                       Requires => InKeys_V1 (J) = InKeys_V2 (J),
                       Ensures  => OutKeys_V1 (J) = OutKeys_V2 (J));

   --  Types and variables for FlipHalves

   type Content is new Integer;
   type H_Type is array (Integer range <>) of Content;

   --  Checking derives annotation of FlipHalves

   procedure FlipHalves (H_V1, H_V2 : in out H_Type; I : Integer) With
     Contract_Case => (Name     => "H(I) from upper half",
                       Mode     => Nominal,
                       Requires =>
                         I in H_V1'Range and then
                         H_V1'First = 1 and then
                         H_V2'First = 1 and then
                         H_V1'Last = H_V2'Last and then
                         I <= H_V1'Last/2 and then
                         H_V1 (I + H_V1'Last/2) = H_V2 (I + H_V2'Last/2),
                       Ensures  => H_V1 (I) = H_V2 (I)),
     Contract_Case => (Name     => "H(I) from lower half",
                       Mode     => Nominal,
                       Requires =>
                         I in H_V1'Range and then
                         H_V1'First = 1 and then
                         H_V2'First = 1 and then
                         H_V1'Last = H_V2'Last and then
                         I > H_V1'Last/2 and then
                         H_V1 (I - H_V1'Last/2) = H_V2 (I - H_V2'Last/2),
                       Ensures  => H_V1 (I) = H_V2 (I));

   --  Types and variables for ArrayPartitionedTransfer

   type Arr is array (Integer range <>) of Integer;

   --  Checking derives annotation of ArrayPartitionedTransfer

   procedure ArrayPartitionedTransfer
     (A_V1, A_V2 : out Arr;
      B_V1, C_V1, B_V2, C_V2 : in Arr;
      K, I : Integer)
   with
     Pre => A_V1'First = 1 and then
            B_V1'First = 1 and then
            C_V1'First = 1 and then
            A_V1'Last = B_V1'Last and then
            A_V1'Last = C_V1'Last and then
            K in B_V1'Range and then
            A_V2'First = 1 and then
            B_V2'First = 1 and then
            C_V2'First = 1 and then
            A_V2'Last = B_V2'Last and then
            A_V2'Last = C_V2'Last and then
            K in B_V2'Range and then
            A_V1'Last = A_V2'Last,
     Contract_Case => (Name     => "A(I) from B(I)",
                       Mode     => Nominal,
                       Requires => I in A_V1'First .. K and then
                                   B_V1 (I) = B_V2 (I),
                       Ensures  => A_V1 (I) = A_V2 (I)),
     Contract_Case => (Name     => "A(I) from C(I-K)",
                       Mode     => Nominal,
                       Requires => I in K+1 .. A_V1'Last and then
                                   C_V1 (I-K) = C_V2 (I-K),
                       Ensures  => A_V1 (I) = A_V2 (I));
end Infoflow;
