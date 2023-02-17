with SPARK.Cut_Operations; use SPARK.Cut_Operations;
procedure Main with SPARK_Mode is

   function Rand (X : Integer) return Boolean with Import;

   --  Functionality: simple uses wit for some and for all

   function F (X : Integer) return Integer with
     Import;

   function Axiom_F_Pos (X : Integer) return Boolean with
     Ghost,
     Import,
     Post => (Axiom_F_Pos'Result = True) and F (X) >= 0;

   function Find_F_Is_3 return Integer with
     Ghost,
     Import,
     Post => F (Find_F_Is_3'Result) = 3;

   procedure Test_1 with Global => null is

   begin
      if Rand (1) then
         pragma Assert
           (for all X in 1 .. 100 => --@ASSERT_PREMISE:PASS
              By (F (X) >= 0, --@ASSERT_STEP:PASS
                  Axiom_F_Pos (X)));
      elsif Rand (2) then
         pragma Assert
           (for all X in 1 .. 100 => --@ASSERT_PREMISE:PASS
              By (F (X) > 0, --@ASSERT_STEP:FAIL
                  Axiom_F_Pos (X)));
      elsif Rand (3) then
         pragma Assert
           (for some X in Integer => --@ASSERT_PREMISE:PASS
              By (F (X) = 3, --@ASSERT_STEP:PASS
                  X = Find_F_Is_3));
      else
         pragma Assert
           (for some X in Integer => --@ASSERT_PREMISE:PASS
              By (X >= 1, --@ASSERT_STEP:FAIL
                  X >= 0));
      end if;
   end Test_1;

   --  Functionality: multiple application of lemmas and proof by case

   procedure Test_2 with Global => null is
      type My_Array is array (Positive range 1 .. 100) of Integer;

      function Find_First_0 (A : My_Array; Fst : Positive) return Natural with
        Import,
        Pre  => Fst in 1 .. A'Last + 1,
        Post => Find_First_0'Result in 0 | Fst .. A'Last;

      function Lemma_Find_First_0_Def (A : My_Array; Fst : Positive) return Boolean with
        Ghost,
        Import,
        Post => (Lemma_Find_First_0_Def'Result = True) and
        (if Find_First_0 (A, Fst) = 0 then (for all I in Fst .. A'Last => A (I) /= 0)
         else Find_First_0 (A, Fst) in Fst .. A'Last
           and then A (Find_First_0 (A, Fst)) = 0
           and then (for all I in Fst .. Find_First_0 (A, Fst) - 1 => A (I) /= 0));

      function Has_Less_Than_3_0 (A : My_Array) return Boolean with
        Ghost,
        Import;

      function Lemma_Has_Less_Than_3_0_Def (A : My_Array) return Boolean with
        Ghost,
        Import,
        Post => (Lemma_Has_Less_Than_3_0_Def'Result = True) and
        Has_Less_Than_3_0 (A)
          = (declare
               Fst_0 : constant Natural := Find_First_0 (A, A'First);
               Snd_0 : constant Natural := Find_First_0 (A, Fst_0 + 1);
               Trd_0 : constant Natural := Find_First_0 (A, Snd_0 + 1);
               For_0 : constant Natural := Find_First_0 (A, Trd_0 + 1);
             begin
                 For_0 = 0);

      procedure Remove_0s (A : in out My_Array) with
        Pre  => Has_Less_Than_3_0 (A),
        Post => Find_First_0 (A, A'First) = 0
      is
         A_Old    : constant My_Array := A with Ghost;
         Fst      : Natural := A'First - 1;
         Prev_Fst : Natural with Ghost;
      begin
         for I in 1 .. 3 loop
            Prev_Fst := Fst + 1;
            Fst := Find_First_0 (A, Fst + 1);
            pragma Assert
              (By (Fst = Find_First_0 (A_Old, Prev_Fst),
                 Lemma_Find_First_0_Def (A_Old, Prev_Fst)
                 and Lemma_Find_First_0_Def (A, Prev_Fst)));
            exit when Fst = 0;
            A (Fst) := 1;
         end loop;
         pragma Assert_And_Cut
           (By
              (By (Find_First_0 (A, A'First) = 0, Lemma_Find_First_0_Def (A, A'First)),
               (declare
                  Fst_0 : constant Natural := Find_First_0 (A_Old, A_Old'First);
                  Snd_0 : constant Natural := Find_First_0 (A_Old, Fst_0 + 1);
                  Trd_0 : constant Natural := Find_First_0 (A_Old, Snd_0 + 1);
                  For_0 : constant Natural := Find_First_0 (A_Old, Trd_0 + 1);
                begin
                  (for all I in A'Range =>
                     By (A (I) /= 0,
                       (if I in Fst_0 | Snd_0 | Trd_0 then So (A (I) = 1, A (I) /= 0)
                        elsif I < Fst_0 or Fst_0 = 0 then By (A_Old (I) /= 0, Lemma_Find_First_0_Def (A_Old, A_Old'First))
                        elsif I < Snd_0 or Snd_0 = 0 then By (A_Old (I) /= 0, Lemma_Find_First_0_Def (A_Old, Fst_0 + 1))
                        elsif I < Trd_0 or Trd_0 = 0 then By (A_Old (I) /= 0, Lemma_Find_First_0_Def (A_Old, Snd_0 + 1))
                        else So
                          (By (For_0 = 0, Lemma_Has_Less_Than_3_0_Def (A_Old)),
                           By (A_Old (I) /= 0, Lemma_Find_First_0_Def (A_Old, Trd_0 + 1)))))))));

         --  Should not be provable after the assert and cut
         pragma Assert (if Find_First_0 (A_Old, A_Old'First) /= 0 then A (Find_First_0 (A_Old, A_Old'First)) = 1); -- ASSERT:FAIL
      end Remove_0s;
   begin
      null;
   end Test_2;

   --  Test splitting of assertions

   procedure Test_Split_1 (A1, B1, A2, B2, A3, B3 : Boolean) with Global => null is
   begin
      if Rand (1) then
         pragma Assume (A1 and A2 and A3);
         pragma Assume (if A1 then B1);
         pragma Assume (if A2 then B2);
         pragma Assume (if A3 then B3);
         pragma Assert (So (A1, B1) and By (B2, A2) and By (B3, A3));
      elsif Rand (2) then
         pragma Assume (A1 and A3);
         pragma Assume (if A1 then B1);
         pragma Assume (if A2 then B2);
         pragma Assume (if A3 then B3);
         pragma Assert (So (A1, B1)
                        and By (B2,
                                A2) --@ASSERT_PREMISE:FAIL
                        and By (B3, A3));
      elsif Rand (3) then
         pragma Assume (A1 and A2 and A3);
         pragma Assume (if A1 then B1);
         pragma Assume (if A3 then B3);
         pragma Assert (So (A1, B1)
                        and By (B2, --@ASSERT_STEP:FAIL
                                A2)
                        and By (B3, A3));
      end if;
   end Test_Split_1;

   procedure Test_Split_2 (A1, B1, A2, B2, A3, B3 : Boolean) with Global => null is
   begin
      if Rand (1) then
         pragma Assume (A1 or A2 or A3);
         pragma Assume (if A1 then B1);
         pragma Assume (if A2 then B2);
         pragma Assume (if A3 then B3);
         pragma Assert (So (A1, B1) or So (A2, B2) or By (B3, A3));
      elsif Rand (2) then
         pragma Assume (if A1 then B1);
         pragma Assume (if A2 then B2);
         pragma Assume (if A3 then B3);
         pragma Assert (So (A1, B1) --@ASSERT_PREMISE:FAIL
                        or So (A2, B2)
                        or By (B3, A3));
      elsif Rand (3) then
         pragma Assume (A3);
         pragma Assume (if A1 then B1);
         pragma Assume (if A2 then B2);
         pragma Assume (if A3 then B3);
         pragma Assert (By (B3, A3)
                        and (So (A1, B1) --@ASSERT_PREMISE:FAIL
                          or So (A2, B2)));
      elsif Rand (4) then
         pragma Assume (A1 or A2 or A3);
         pragma Assume (if A1 then B1);
         pragma Assume (if A3 then B3);
         pragma Assert (So (A1, B1)
                        or So (A2,
                               B2) --@ASSERT_STEP:FAIL
                        or By (B3, A3));
      end if;
   end Test_Split_2;

   --  Test that each conclusion is checked in the context of its pre

   procedure Test_RTE_1 with Global => null is
      function A1 return Boolean with Import;
      function B1 return Boolean with Import,
        Pre => A1;
      function A2 return Boolean with Import,
        Pre => A1;
      function B2 return Boolean with Import,
        Pre => A1 and then A2 and then B1;
   begin
      if Rand (1) then
         pragma Assert (So (A1, --@ASSERT_PREMISE:FAIL
                            B1) --@ASSERT_STEP:FAIL @PRECONDITION:PASS
                        and By (B2, --@ASSERT_STEP:FAIL @PRECONDITION:FAIL
                                A2)); --@PRECONDITION:FAIL
      elsif Rand (2) then
         pragma Assert (So (A1,
                            B1) --@ASSERT_STEP:FAIL @PRECONDITION:PASS
                        and then By (B2, --@ASSERT_STEP:FAIL @PRECONDITION:PASS
                                     A2)); --@ASSERT_PREMISE:FAIL @PRECONDITION:PASS
      else
         pragma Assert (By (B1, --@ASSERT_STEP:FAIL @PRECONDITION:PASS
                            A1) --@ASSERT_PREMISE:FAIL
                        and then By (B2, --@ASSERT_STEP:FAIL @PRECONDITION:FAIL
                                     A2)); --@PRECONDITION:FAIL
      end if;
   end Test_RTE_1;

   procedure Test_RTE_2 with Global => null is
      function A1 return Boolean with Import;
      function B1 return Boolean with Import,
        Pre => A1;
      function A2 return Boolean with Import,
        Pre => not A1 or else not B1;
      function B2 return Boolean with Import,
        Pre => not A1 or else (not B1 and then A2);
   begin
      if Rand (1) then
         pragma Assert (By (B1, --@ASSERT_PREMISE:FAIL @ASSERT_STEP:FAIL @PRECONDITION:PASS
                            A1)
                        or By (B2, --@ASSERT_STEP:FAIL @PRECONDITION:FAIL
                               A2)); --@PRECONDITION:FAIL
      elsif Rand (2) then
         pragma Assert (By (B1, --@ASSERT_PREMISE:FAIL @ASSERT_STEP:FAIL @PRECONDITION:PASS
                            A1)
                        or else By (B2, --@ASSERT_STEP:FAIL @PRECONDITION:PASS
                                    A2)); --@PRECONDITION:PASS
      else
         pragma Assert (So (A1, --@ASSERT_PREMISE:FAIL
                            B1) --@ASSERT_STEP:FAIL @PRECONDITION:PASS
                        or else By (B2, --@ASSERT_STEP:FAIL @PRECONDITION:PASS
                                    A2)); --@PRECONDITION:PASS
      end if;
   end Test_RTE_2;

   --  Test dead branch warning

   procedure Test_Unreachable_Branch (A1, B1, A2, B2 : Boolean) with Global => null is
      C : Integer := 10;
   begin
      if Rand (1) then
         pragma Assume (if A1 then B1);
         pragma Assume (if A2 then B2);
         pragma Assume (if A2 then A1);
         pragma Assert (if A1 then So (A1, B1)
                        elsif A2 then By (B2, A2) -- dead branch
                        elsif not A1 then True
                        else True); -- dead branch but no warnings
      elsif Rand (2) then
         pragma Assume (if A1 then B1);
         pragma Assume (if A2 then B2);
         pragma Assume (if not A1 then A2);
         pragma Assert (if A1 then So (A1, B1)
                        elsif not A1 then By (B2, A2)
                        else False); -- dead branch
      elsif Rand (3) then
         pragma Assume (if A1 then B1);
         pragma Assume (if A2 then B2);
         pragma Assume (if A2 then A1);
         pragma Assert (case A1 is
                           when True  => So (A1, B1),
                           when False =>
                          (case A2 is
                              when True  => By (B2, A2), -- dead branch
                              when False => True));
      elsif Rand (4) then
         pragma Assume (if A2 then A1);
         if not A1 then
            C := 0;
         end if;
         pragma Assert (for all X in 1 .. 10 when A2 and then X > C => By (X > 5, A1)); -- dead branch
      end if;
   end Test_Unreachable_Branch;
begin
   null;
end;
