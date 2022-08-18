package body test_multiset with SPARK_Mode => On is

   procedure Test_Basic_Operations with SPARK_Mode => On is
      N, M : Multiset;
   begin
      --  Is_Empty

      pragma Assert (Is_Empty (M));
      M := Add (M, 1);
      pragma Assert (not Is_Empty (M));
      M := Remove_All (M, 1);
      pragma Assert (Is_Empty (M));

      --  Cardinality & Nb_Occurence & Contains

      pragma Assert (Cardinality (M) = 0);
      pragma Assert (Nb_Occurence (M, 1) = 0);
      pragma Assert (not Contains (M, 1));
      M := Add (M, 1, 4);
      pragma Assert (Cardinality (M) = 4);
      pragma Assert (Nb_Occurence (M, 1) = 4);
      pragma Assert (Contains (M, 1));

      pragma Assert (not Contains (M, 2));
      pragma Assert (Nb_Occurence (M, 2) = 0);
      M := Add (M, 2, 5);
      pragma Assert (Cardinality (M) = 9);
      pragma Assert (Contains (M, 2));
      pragma Assert (Nb_Occurence (M, 2) = 5);

      pragma Check (Proof_Only, False);
   end Test_Basic_Operations;

   procedure Test_Basic_Properties with SPARK_Mode => On is
      M, N : Multiset;
   begin
      --  <=

      M := Add (M, 1, 4);
      M := Add (M, 2, 5);


      pragma Assert (N <= M);
      pragma Assert (not (M <= N));
      N := M;
      pragma Assert (N <= M and then M <= N);

      M := Add (M, 1, 1);
      pragma Assert (N <= M);
      pragma Assert (not (M <= N));

      N := Add (N, 1, 2);
      pragma Assert (M <= N);
      pragma Assert (not (N <= M));

      M := Add (M, 3, 1);
      pragma Assert (Cardinality (M) = Cardinality (N));
      pragma Assert (not (M <= N));
      pragma Assert (not (N <= M));

      --  =

      pragma Assert (M /= N);
      N := Add (N, 3, 1);
      pragma Assert (Nb_Occurence (N, 3) = Nb_Occurence (M, 3));
      pragma Assert (M /= N);
      pragma Assert (Nb_Occurence (M, 1) = 5);
      pragma Assert (Nb_Occurence (N, 1) = 6);
      M := Add (M, 1, 1);
      pragma Assert (Nb_Occurence (M, 1) = Nb_Occurence (N, 1));
      pragma Assert (M <= N and N <= M);
      pragma Assert (M = N);

      pragma Check (Proof_Only, False);
   end Test_Basic_Properties;

   procedure Test_Properties with SPARK_Mode => On is
      M, N, S : Multiset;
   begin
      --  Equal_Except

      M := Empty_Multiset;
      N := Empty_Multiset;

      pragma Assert (Is_Empty (M));

      pragma Assert (Cardinality (M) = 0);
      pragma Warnings (Off, "unused variable ""E""");
      pragma Assert (for all E of M => False);
      pragma Warnings (On, "unused variable ""E""");
      pragma Assert (not Contains (M, 1));
      N := Add (N, 1, 1);
      pragma Assert (Nb_Occurence (N, 1) = 1);
      N := Add (N, 2, 2);
      N := Add (N, 3, 3);

      M := Add (M, 3, 3);
      M := Add (M, 2, 2);
      M := Add (M, 1, 1);
      pragma Assert (Nb_Occurence (N, 1) = 1);
      pragma Assert (Nb_Occurence (M, 1) = 1);
      pragma Assert (Nb_Occurence (N, 1) = Nb_Occurence (M, 1));
      pragma Assert (Nb_Occurence (N, 2) = Nb_Occurence (M, 2));
      pragma Assert (Nb_Occurence (N, 3) = Nb_Occurence (M, 3));

      pragma Assert (M = N);

      M := Add (M, 1, 1);

      pragma Assert (Equal_Except (M, N, 1));
      pragma Assert (Equal_Except (N, M, 1));
      pragma Assert (not Equal_Except (M, N, 2));

      N := Add (N, 1, 1);

      pragma Assert (M = N);

      M := Add (M, 4, 4);

      pragma Assert (M /= N);
      pragma Assert (Equal_Except (M, N, 4));

      --  Included_Except

      M := Empty_Multiset;
      N := Empty_Multiset;

      M := Add (M, 1, 2);
      N := Add (N, 1);
      N := Add (N, 2);

      pragma Assert (not (N <= M));
   end Test_Properties;

   procedure Test_Basic_Constructors is
      M, N : Multiset;
   begin
      -- Is_Empty

      M := Empty_Multiset;

      pragma Assert (Is_Empty (M));
      pragma Warnings (Off, "unused variable ""E""");
      pragma Assert (for all E of M => False);
      pragma Warnings (Off, "unused variable ""E""");
      pragma Assert (Cardinality (M) = 0);
   end Test_Basic_Constructors;

   procedure Test_Operations is
      M, N, S : Multiset;
   begin

      --  Choose

      M := Add (M, 2);
      pragma Assert (Choose (M) = 2);

      M := Add (M, 3);
      pragma Assert (Choose (M) = 2 or else Choose (M) = 3);

      --  Add

      M := Empty_Multiset;

      pragma Assert (Cardinality (M) = 0);

      M := Add (M, 1);

      pragma Assert (Nb_Occurence (M, 1) = 1);
      pragma Assert (Cardinality (M) = 1);

      M := Add (M, 2, 3);

      pragma Assert (Cardinality (M) = 4);
      pragma Assert (Nb_Occurence (M, 1) = 1);
      pragma Assert (Nb_Occurence (M, 2) = 3);

      M := Add (M, 4, 3);

      pragma Assert (Cardinality (M) = 7);
      pragma Assert (Nb_Occurence (M, 1) = 1);
      pragma Assert (Nb_Occurence (M, 2) = 3);
      pragma Assert (Nb_Occurence (M, 4) = 3);

      -- Remove_All

      M := Remove_All (M, 4);
      pragma Assert (Cardinality (M) = 4);
      pragma Assert (Nb_Occurence (M, 4) = 0);
      pragma Assert (Nb_Occurence (M, 2) = 3);
      pragma Assert (Nb_Occurence (M, 1) = 1);

      M := Remove_All (M, 2);
      pragma Assert (Cardinality (M) = 1);
      pragma Assert (Nb_Occurence (M, 4) = 0);
      pragma Assert (Nb_Occurence (M, 2) = 0);
      pragma Assert (Nb_Occurence (M, 1) = 1);

      M := Remove_All (M, 1);
      pragma Assert (Is_Empty (M));

      --  Remove

      M := Add (M, 1);
      pragma Assert (Nb_Occurence (M, 1) = 1);
      M := Add (M, 2, 3);
      M := Add (M, 3, 5);
      pragma Assert (Nb_Occurence (M, 2) = 3);
      M := Remove (M, 2);
      pragma Assert (Nb_Occurence (M, 3) = 5);
      M := Remove (M, 3, 2);

      pragma Assert (Nb_Occurence (M, 1) = 1);
      pragma Assert (Nb_Occurence (M, 2) = 2);
      pragma Assert (Nb_Occurence (M, 3) = 3);

      pragma Assert
        (for all E of M =>
           Nb_Occurence (M, E) = To_Big_Integer (Natural (E)));

      --  "-"

      M := Empty_Multiset;
      N := Empty_Multiset;

      M := Add (M, 1, 3);
      N := Add (N, 1, 2);

      M := Add (M, 2, 3);
      N := Add (N, 2);

      M := Add (M, 3);
      N := Add (N, 4);


      S := M - N;

      pragma Assert (S <= M);
      pragma Assert (Nb_Occurence (S, 1) = 1);
      pragma Assert (Nb_Occurence (S, 2) = 2);
      pragma Assert (Contains (S, 3));
      pragma Assert (not Contains (S, 4));

      --  Union

      M := Empty_Multiset;
      N := Empty_Multiset;

      M := Add (M, 1);
      N := Add (N, 2, 2);
      M := Add (M, 3, 2);
      N := Add (N, 3);

      S := Sum (M, N);

      pragma Assert (Cardinality (S) = 6);
      pragma Assert (Nb_Occurence (S, 1) = 1);
      pragma Assert (Nb_Occurence (S, 2) = 2);
      pragma Assert (Nb_Occurence (S, 3) = 3);
      pragma Assert (M <= S);
      pragma Assert (N <= S);

      --  Intersection

      S := Intersection (M, N);

      pragma Assert (Nb_Occurence (S, 3) = 1);
      pragma Assert (Cardinality (S) <= 3);

      pragma Check (Proof_Only, False);
   end Test_Operations;

end test_multiset;
