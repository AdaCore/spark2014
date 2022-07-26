--  Test that we do not create unsoundness because of recursivity in proof
--  of modules with automatically instantiated lemmas.

procedure Test_Bad with SPARK_Mode is
   --  This test is used to make sure that automatically instantiated lemmas
   --  are never used to prove themselves.

   package Test_Rec_1 is
      function P (X : Natural) return Boolean with
        Ghost,
        Annotate => (GNATprove, Always_Return),
        Global => null,
        Import;
      --  An unknown property

      function F (X : Natural) return Integer is (X);
      --  Any function on which the lemma is attached

      procedure Lemma_Prove_P (X : Natural) with
        Ghost,
        Annotate => (GNATprove, Automatic_Instantiation),
        Post => P (X); -- @POSTCONDITION:FAIL
      --  A lemma using the function F to prove P (X).
      --  It should not be provable as Lemma_Prove_P should not be available to
      --  prove itself.
   end Test_Rec_1;

   package body Test_Rec_1 is
      procedure Lemma_Prove_P (X : Natural) is
         Y : Integer;
      begin
         Y := F (X);
      end Lemma_Prove_P;
   end Test_Rec_1;

   --  This test is used to make sure that automatically instantiated lemmas
   --  are never used to prove subprograms that they call.

   package Test_Rec_2 is
      function P (X : Natural) return Boolean with
        Ghost,
        Annotate => (GNATprove, Always_Return),
        Global => null,
        Import;
      --  An unknown property

      function F (X : Natural) return Integer is (X);
      --  Any function on which the lemma is attached

      procedure Lemma_Prove_P (X : Natural) with
        Ghost,
        Annotate => (GNATprove, Automatic_Instantiation),
        Post => P (X);
      --  A lemma using the function G to prove P (X)

      function G (X : Natural) return Boolean is
        (F (X) = X)
          with Post => G'Result and then P (X); -- @POSTCONDITION:FAIL
      --  The postcondition of G should not be provable as Lemma_Prove_P should
      --  not be available for the proof of G.
   end Test_Rec_2;

   package body Test_Rec_2 is
      procedure Lemma_Prove_P (X : Natural) is
         R : Boolean;
      begin
         R := G (X);
      end Lemma_Prove_P;
   end Test_Rec_2;

   --  This test is used to make sure that automatically instantiated lemmas
   --  are never used to prove other automatically instanciated lemmas of the
   --  same subprogram.

   package Test_Rec_3 is
      function P (X : Natural) return Boolean with
        Ghost,
        Annotate => (GNATprove, Always_Return),
        Global => null,
        Import;
      --  An unknown property

      function F (X : Natural) return Integer is (X);
      --  Any function on which the lemmas are attached

      procedure Lemma_Prove_P1 (X : Natural) with
        Ghost,
        Annotate => (GNATprove, Automatic_Instantiation),
        Post => P (X); -- @POSTCONDITION:FAIL
      --  A lemma using the function F to prove P (X).
      --  It should not be provable as Lemma_Prove_P2 should not be available
      --  to prove other lemmas of the same subprogram.

      procedure Lemma_Prove_P2 (X : Natural) with
        Ghost,
        Annotate => (GNATprove, Automatic_Instantiation),
        Post => P (X); -- @POSTCONDITION:FAIL
      --  A lemma using the function F to prove P (X).
      --  It should not be provable as Lemma_Prove_P1 should not be available
      --  to prove other lemmas of the same subprogram.
   end Test_Rec_3;

   package body Test_Rec_3 is
      procedure Lemma_Prove_P1 (X : Natural) is
         Y : Integer;
      begin
         Y := F (X);
      end Lemma_Prove_P1;
      procedure Lemma_Prove_P2 (X : Natural) is
         Y : Integer;
      begin
         Y := F (X);
      end Lemma_Prove_P2;
   end Test_Rec_3;

   --  This test is used to make sure that automatically instantiated lemmas
   --  of different functions are never used to prove each other recursively.

   package Test_Rec_4 is
      function P (X : Natural) return Boolean with
        Ghost,
        Annotate => (GNATprove, Always_Return),
        Global => null,
        Import;
      --  An unknown property

      function F (X : Natural) return Integer is (X);
      --  Any function on which the lemmas are attached

      procedure Lemma_Prove_P1 (X : Natural) with
        Ghost,
        Annotate => (GNATprove, Automatic_Instantiation),
        Post => P (X);

      procedure Lemma_Prove_P2 (X : Natural) with
        Ghost,
        Post => P (X); -- @POSTCONDITION:FAIL
      --  A lemma using the function G to prove P (X).
      --  It should not be provable as Lemma_Prove_P3 should not be available
      --  as Lemma_Prove_P2 is lemma-recursive with G.

      function G (X : Natural) return Integer is (X);
      --  Any function on which the lemmas are attached

      procedure Lemma_Prove_P3 (X : Natural) with
        Ghost,
        Annotate => (GNATprove, Automatic_Instantiation),
        Post => P (X);

      procedure Lemma_Prove_P4 (X : Natural) with
        Ghost,
        Post => P (X); -- @POSTCONDITION:FAIL
      --  A lemma using the function F to prove P (X).
      --  It should not be provable as Lemma_Prove_P1 should not be available
      --  as Lemma_Prove_P4 is lemma-recursive with F.
   end Test_Rec_4;

   package body Test_Rec_4 is
      procedure Lemma_Prove_P1 (X : Natural) is
      begin
         Lemma_Prove_P2 (X);
      end Lemma_Prove_P1;
      procedure Lemma_Prove_P2 (X : Natural) is
         Y : Integer;
      begin
         Y := G (X);
      end Lemma_Prove_P2;
      procedure Lemma_Prove_P3 (X : Natural) is
      begin
         Lemma_Prove_P4 (X);
      end Lemma_Prove_P3;
      procedure Lemma_Prove_P4 (X : Natural) is
         Y : Integer;
      begin
         Y := F (X);
      end Lemma_Prove_P4;
   end Test_Rec_4;

   --  This test is used to make sure that potentially non-returning lemma
   --  procedures are never automatically instantiated.

   package Test_No_Return is
      function P (X : Natural) return Boolean with
        Ghost,
        Annotate => (GNATprove, Always_Return),
        Global => null,
        Import;
      --  An unknown property

      function F (X : Natural) return Integer is (X);
      --  Any function on which the lemma is attached

      procedure Lemma_Prove_P (X : Natural) with
        Ghost,
        Annotate => (GNATprove, Automatic_Instantiation),
        Post => P (X);
      --  Potentially non-returning lemma

      procedure Lemma_Prove_P2 (X : Natural) with
        Ghost,
        Post => P (X); -- @POSTCONDITION:FAIL
      --  A lemma using the function F to prove P (X).
      --  It should not be provable as Lemma_Prove_P should not be available as
      --  it might not return.
   end Test_No_Return;

   package body Test_No_Return is
      procedure Lemma_Prove_P (X : Natural) is
      begin
         if not P (X) then
            loop
               null;
            end loop;
         end if;
      end Lemma_Prove_P;
      procedure Lemma_Prove_P2 (X : Natural) is
         Y : Integer;
      begin
         Y := F (X);
      end Lemma_Prove_P2;
   end Test_No_Return;
begin
   null;
end Test_Bad;
