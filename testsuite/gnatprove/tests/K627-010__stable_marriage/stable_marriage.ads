package Stable_Marriage with SPARK_Mode is

   Last_Id : constant := 64;
   type Group1_Id is range 1 .. Last_Id;
   type Group2_Id is range 1 .. Last_Id;
   type Ranking is range 1 .. Last_Id;
   -- Ranking'First =>  most preferred, Ranking'Last => least preferred

   type Ranking_Of_Group1 is array (Ranking) of Group1_Id;
   type Ranking_Of_Group2 is array (Ranking) of Group2_Id;

   type Ranking_Of_Group2_By_Group1 is
     array (Group1_Id) of Ranking_Of_Group2;
   type Ranking_Of_Group1_By_Group2 is
     array (Group2_Id) of Ranking_Of_Group1;

   type G1_To_G2_Map is array (Group1_Id) of Group2_Id;
   type G2_To_G1_Map is array (Group2_Id) of Group1_Id;

   function Is_Permutation_1 (R1 : Ranking_Of_Group1) return Boolean with
     Post => Is_Permutation_1'Result =
       (for all G1 in Group1_Id =>
          (for some Rank in Ranking => (R1 (Rank) = G1)));

   procedure Invert_Permutation_1 (R1 : Ranking_Of_Group1) with
     Depends => (null => R1),
     Pre     => Is_Permutation_1 (R1),
     Post    => (for all Rank1 in Ranking =>
                   (for all Rank2 in Ranking =>
                        (if Rank1 /= Rank2 then R1 (Rank1) /= R1 (Rank2))));

   function Is_Permutation_2 (R2 : Ranking_Of_Group2) return Boolean with
     Post => Is_Permutation_2'Result =
       (for all G2 in Group2_Id =>
          (for some Rank in Ranking => (R2 (Rank) = G2)));

   procedure Invert_Permutation_2 (R2 : Ranking_Of_Group2) with
     Depends => (null => R2),
     Pre     => Is_Permutation_2 (R2),
     Post    => (for all Rank1 in Ranking =>
                   (for all Rank2 in Ranking =>
                        (if Rank1 /= Rank2 then R2 (Rank1) /= R2 (Rank2))));

   type Inverted_Ranking_Of_Group1 is array (Group1_Id) of Ranking;
   type Inverted_Ranking_Of_Group2 is array (Group2_Id) of Ranking;

   function Invert_1 (R1 : Ranking_Of_Group1)
                      return Inverted_Ranking_Of_Group1 with
     Pre => Is_Permutation_1 (R1),
     Post => (for all Rank in Ranking => (Invert_1'Result (R1 (Rank)) = Rank)) and
     (for all G1 in Group1_Id => (R1 (Invert_1'Result (G1)) = G1));

   function Invert_2 (R2 : Ranking_Of_Group2)
                       return Inverted_Ranking_Of_Group2 with
     Pre => Is_Permutation_2 (R2),
     Post => (for all Rank in Ranking => (Invert_2'Result (R2 (Rank)) = Rank)) and
     (for all G2 in Group2_Id => (R2 (Invert_2'Result (G2)) = G2));

   procedure Invert_Ranking_Of_Group_1 (G2_To_G1 : G2_To_G1_Map) with
     Depends => (null => G2_To_G1),
     Pre     => (for all G1 in Group1_Id =>
                   (for some G2 in Group2_Id => (G2_To_G1 (G2) = G1))),
     Post    => (for all G21 in Group2_Id =>
                   (for all G22 in Group2_Id =>
                        (if G21 /= G22 then G2_To_G1 (G21) /= G2_To_G1 (G22))));

   function Invert_Map (G2_To_G1 : G2_To_G1_Map) return G1_To_G2_Map with
   Pre => (for all G1 in Group1_Id =>
             (for some G2 in Group2_Id => (G2_To_G1 (G2) = G1))),
   Post =>
      ((for all G1 in Group1_Id => (G2_To_G1 (Invert_Map'Result (G1)) = G1)) and
       (for all G2 in Group2_Id => (Invert_Map'Result (G2_To_G1 (G2)) = G2)));

   function Is_Preferred_1 (G1_A, G1_B : Group1_Id; R1 : Ranking_Of_Group1)
                            return Boolean with
     Pre => Is_Permutation_1 (R1),
     Post => Is_Preferred_1'Result =
       (Invert_1 (R1) (G1_A) <= Invert_1 (R1) (G1_B));

   function Is_Preferred_2 (G2_A, G2_B : Group2_Id; R2 : Ranking_Of_Group2)
                             return Boolean with
     Pre => Is_Permutation_2 (R2),
     Post => Is_Preferred_2'Result =
       (Invert_2 (R2) (G2_A) <= Invert_2 (R2) (G2_B));

   -- note that Is_Prefered_x returns True if first two arguments are equal

   function Matching
     (Ranking_1 : Ranking_Of_Group2_By_Group1;
      Ranking_2 : Ranking_Of_Group1_By_Group2)
       return G2_To_G1_Map with
     Pre => (for all G1 in Group1_Id => (Is_Permutation_2 (Ranking_1 (G1)))) and
     (for all G2 in Group2_Id => (Is_Permutation_1 (Ranking_2 (G2)))),
     Post =>
       (for all G1 in Group1_Id =>
          (for some G2 in Group2_Id => (Matching'Result (G2) = G1))) and then
     (for all G1 in Group1_Id =>
        (for all G2 in Group2_Id =>
             ((Is_Preferred_2
               (Invert_Map (Matching'Result) (G1), G2, Ranking_1 (G1))) or
                (Is_Preferred_1 (Matching'Result (G2), G1, Ranking_2 (G2))))));

end Stable_Marriage;
