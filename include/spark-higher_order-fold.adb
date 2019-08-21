------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--              S P A R K . H I G H E R _ O R D E R . F O L D               --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2018, AdaCore                        --
--                                                                          --
-- SPARK is free software;  you can  redistribute it and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion. SPARK is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.                                     --
--                                                                          --
-- As a special exception under Section 7 of GPL version 3, you are granted --
-- additional permissions described in the GCC Runtime Library Exception,   --
-- version 3.1, as published by the Free Software Foundation.               --
--                                                                          --
-- You should have received a copy of the GNU General Public License and    --
-- a copy of the GCC Runtime Library Exception along with this program;     --
-- see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see    --
-- <http://www.gnu.org/licenses/>.                                          --
--                                                                          --
------------------------------------------------------------------------------

package body SPARK.Higher_Order.Fold with SPARK_Mode is

   -----------
   -- Count --
   -----------

   package body Count is

      ----------------
      -- Count_Zero --
      ----------------

      procedure Count_Zero (A : Array_Type) with SPARK_Mode =>
#if SPARK_BODY_MODE="On"
          On
#else
          Off
#end if;
      is
      begin
         for I in A'Range loop
            pragma Loop_Invariant
              ((Count_Left.Acc.Fold (A, 0) (I) = 0) =
               (for all K in A'First .. I =>
                     not Choose (A (K))));
         end loop;
      end Count_Zero;

      ------------------
      -- Update_Count --
      ------------------

      procedure Update_Count (A1, A2 : Array_Type; I : Index_Type) with
        SPARK_Mode =>
#if SPARK_BODY_MODE="On"
          On
#else
          Off
#end if;
      is
         C : constant Integer :=
           (if (Choose (A1 (I)) and Choose (A2 (I)))
            or (not Choose (A1 (I)) and not Choose (A2 (I))) then 0
            elsif  Choose (A1 (I)) then 1
            else -1);
      begin
         for K in A1'Range loop
            pragma Loop_Invariant
              (if K < I then
                    Count_Left.Acc.Fold (A1, 0) (K) =
                    Count_Left.Acc.Fold (A2, 0) (K)
               else
                    Count_Left.Acc.Fold (A1, 0) (K) =
                    Count_Left.Acc.Fold (A2, 0) (K) + C);
         end loop;
         pragma Assert
           (Count_Left.Acc.Fold (A1, 0) (A1'Last) =
            Count_Left.Acc.Fold (A2, 0) (A1'Last) + C);
      end Update_Count;

   end Count;

   -------------
   -- Count_2 --
   -------------

   package body Count_2 is

      ----------------
      -- Count_Zero --
      ----------------

      procedure Count_Zero (A : Array_Type) with SPARK_Mode =>
#if SPARK_BODY_MODE="On"
          On
#else
          Off
#end if;
      is
      begin
         if A'Length (2) > 0 then
            for I in A'Range (1) loop
               pragma Loop_Invariant
                 (if I > A'First (1) then
                      (Fold_Count.Acc.Fold (A, 0) (I - 1, A'Last (2)) = 0) =
                  (for all K in A'First (1) .. I - 1 =>
                       (for all L in A'Range (2) => not Choose (A (K, L)))));
               for J in A'Range (2) loop
                  pragma Loop_Invariant
                    ((Fold_Count.Acc.Fold (A, 0) (I, J) = 0) =
                     ((if I > A'First (1) then
                            (for all K in A'First (1) .. I - 1 =>
                               (for all L in A'Range (2) =>
                                     not Choose (A (K, L)))))
                        and (for all L in A'First (2) .. J =>
                             not Choose (A (I, L)))));
               end loop;
            end loop;
         end if;
      end Count_Zero;

      ------------------
      -- Update_Count --
      ------------------

      procedure Update_Count (A1, A2 : Array_Type; I : Index_1; J : Index_2)
      with SPARK_Mode =>
#if SPARK_BODY_MODE="On"
          On
#else
          Off
#end if;
      is
         C : constant Integer :=
           (if (Choose (A1 (I, J)) and Choose (A2 (I, J)))
            or (not Choose (A1 (I, J)) and not Choose (A2 (I, J))) then 0
            elsif  Choose (A1 (I, J)) then 1
            else -1);
      begin
         for K in A1'Range (1) loop
            pragma Loop_Invariant
              (if K < I  or else (K = I and then A1'First (2) < J) then
                    Fold_Count.Acc.Fold (A1, 0) (K, A1'First (2)) =
                    Fold_Count.Acc.Fold (A2, 0) (K, A1'First (2))
               else
                    Fold_Count.Acc.Fold (A1, 0) (K, A1'First (2)) =
                   Fold_Count.Acc.Fold (A2, 0) (K, A1'First (2)) + C);
            pragma Assert
              (if K > A1'First (1) then
                    In_Range (A2, (Fold_Count.Acc.Fold (A2, 0)
                 (K - 1, A1'Last (2))), K, A1'First (2)));
            for L in A1'Range (2) loop
               pragma Loop_Invariant
                 (if L > A1'First (2) then
                       In_Range (A2, (Fold_Count.Acc.Fold (A2, 0)
                    (K, L - 1)), K, L));
               pragma Loop_Invariant
                 (if K < I or else (K = I and then L < J) then
                       Fold_Count.Acc.Fold (A1, 0) (K, L) =
                       Fold_Count.Acc.Fold (A2, 0) (K, L)
                  else
                       Fold_Count.Acc.Fold (A1, 0) (K, L) =
                       Fold_Count.Acc.Fold (A2, 0) (K, L) + C);
            end loop;
         end loop;
         pragma Assert
           (Fold_Count.Acc.Fold (A1, 0) (A1'Last (1), A1'Last (2)) =
            Fold_Count.Acc.Fold (A2, 0) (A1'Last (1), A1'Last (2)) + C);
      end Update_Count;
   end Count_2;

   ------------
   -- Fold_2 --
   ------------

   package body Fold_2 is

      ----------
      -- Fold --
      ----------

      function Fold (A : Array_Type; Init : Element_Out) return Element_Out
      with SPARK_Mode =>
#if SPARK_BODY_MODE="On"
          On
#else
          Off
#end if;
      is
      begin
         return R : Element_Out := Init do
            if A'Length (2) > 0 then
               for I in A'Range (1) loop
                  pragma Loop_Invariant
                    (Ind_Prop (A, R, I, A'First (2))
                     and then F (A (I, A'First (2)), R) =
                         Acc.Fold (A, Init) (I, A'First (2)));
                  for J in A'Range (2) loop
                     pragma Loop_Invariant
                       (Ind_Prop (A, R, I, J)
                        and then F (A (I, J), R) = Acc.Fold (A, Init) (I, J));
                     if J /= A'Last (2) then
                        Acc.Prove_Ind_Col (A, R, I, J);
                     elsif I /= A'Last (1) then
                        Acc.Prove_Ind_Row (A, R, I);
                     end if;

                     R := F (A (I, J), R);
                  end loop;
               end loop;
            end if;
         end return;
      end Fold;
   end Fold_2;

   ----------------
   -- Fold_2_Acc --
   ----------------

   package body Fold_2_Acc is

      ----------
      -- Fold --
      ----------

      function Fold (A : Array_Type; Init : Element_Out) return Acc_Array with
        SPARK_Mode =>
#if SPARK_BODY_MODE="On"
          On
#else
          Off
#end if;
      is
         Acc : Element_Out := Init;
      begin
         return R : Acc_Array (A'Range (1), A'Range (2)) :=
           (others => (others => Init))
         do
            for I in A'Range (1) loop
               pragma Loop_Invariant
                 (if I = A'First (1) then Acc = Init
                  else Acc = R (I - 1, A'Last (2)));
               pragma Loop_Invariant (Ind_Prop (A, Acc, I, A'First (2)));
               pragma Loop_Invariant
                 (if I > A'First (1) then
                       Ind_Prop (A, Init, A'First (1), A'First (2))
                  and then R (A'First (1), A'First (2)) =
                    F (A (A'First (1), A'First (2)), Init));
               pragma Loop_Invariant
                 (for all K in A'Range (1) =>
                      (if K < I and then K > A'First (1) then
                         Ind_Prop (A, R (K - 1, A'Last (2)), K, A'First (2))
                       and then R (K, A'First (2)) =
                         F (A (K, A'First (2)), R (K - 1, A'Last (2)))));
               pragma Loop_Invariant
                 (for all K in A'Range (1) =>
                      (for all L in A'Range (2) =>
                         (if K < I and then L > A'First (2) then
                               Ind_Prop (A, R (K, L - 1), K, L)
                          and then R (K, L) = F (A (K, L), R (K, L - 1)))));
               for J in A'Range (2) loop
                  pragma Loop_Invariant
                    (if I > A'First (1) or else J > A'First (2) then
                          Ind_Prop (A, Init, A'First (1), A'First (2))
                     and then R (A'First (1), A'First (2)) =
                       F (A (A'First (1), A'First (2)), Init));
                  pragma Loop_Invariant
                    (for all K in A'Range (1) =>
                         (if K > A'First (1) and then
                            (K < I or else (K = I and then J > A'First (2)))
                          then
                            Ind_Prop (A, R (K - 1, A'Last (2)), K, A'First (2))
                          and then R (K, A'First (2)) =
                            F (A (K, A'First (2)), R (K - 1, A'Last (2)))));
                  pragma Loop_Invariant
                    (for all K in A'Range (1) =>
                         (for all L in A'Range (2) =>
                            (if L > A'First (2) and then
                                 (K < I or else (K = I and then L < J))
                             then
                                Ind_Prop (A, R (K, L - 1), K, L)
                             and then R (K, L) = F (A (K, L), R (K, L - 1)))));
                  pragma Loop_Invariant
                    (if J /= A'First (2) then Acc = R (I, J - 1)
                     elsif I /= A'First (1) then Acc = R (I - 1, A'Last (2))
                     else Acc = Init);
                  pragma Loop_Invariant (Ind_Prop (A, Acc, I, J));
                  R (I, J) := F (A (I, J), Acc);
                  if J < A'Last (2) then
                     Prove_Ind_Col (A, Acc, I, J);
                  elsif I < A'Last (1) then
                     Prove_Ind_Row (A, Acc, I);
                  else
                     Prove_Last (A, Acc);
                  end if;
                  Acc := R (I, J);
               end loop;
            end loop;
            pragma Assert
              (for all K in A'Range (1) =>
                   (if K > A'First (1) then
                           Ind_Prop (A, R (K - 1, A'Last (2)), K, A'First (2))
                    and then R (K, A'First (2)) =
                      F (A (K, A'First (2)), R (K - 1, A'Last (2)))));
         end return;
      end Fold;

      -------------------
      -- Prove_Ind_Col --
      -------------------

      procedure Prove_Ind_Col
        (A : Array_Type; X : Element_Out; I : Index_1; J : Index_2)
      is null;

      -------------------
      -- Prove_Ind_Row --
      -------------------

      procedure Prove_Ind_Row (A : Array_Type; X : Element_Out; I : Index_1)
      is null;

      ----------------
      -- Prove_Last --
      ----------------

      procedure Prove_Last (A : Array_Type; X : Element_Out) is null;

   end Fold_2_Acc;

   ---------------
   -- Fold_Left --
   ---------------

   package body Fold_Left is

      ----------
      -- Fold --
      ----------

      function Fold (A : Array_Type; Init : Element_Out) return Element_Out
        with SPARK_Mode =>
#if SPARK_BODY_MODE="On"
          On
#else
          Off
#end if;
      is
      begin
         return R : Element_Out := Init do
            for I in A'Range loop
               pragma Loop_Invariant
                 (Ind_Prop (A, R, I)
                  and then F (A (I), R) = Acc.Fold (A, Init) (I));
               if I /= A'Last then
                  Acc.Prove_Ind (A, R, I);
               end if;
               R := F (A (I), R);
            end loop;
         end return;
      end Fold;
   end Fold_Left;

   -------------------
   -- Fold_Left_Acc --
   -------------------

   package body Fold_Left_Acc is

      ----------
      -- Fold --
      ----------

      function Fold (A : Array_Type; Init : Element_Out) return Acc_Array
        with SPARK_Mode =>
#if SPARK_BODY_MODE="On"
          On
#else
          Off
#end if;
      is
         Acc : Element_Out := Init;
      begin
         return R : Acc_Array (A'First .. A'Last) := (others => Init) do
            for I in A'Range loop
               pragma Assert (Ind_Prop (A, Acc, I));
               R (I) := F (A (I), Acc);
               pragma Loop_Invariant
                 (Ind_Prop (A, Init, A'First)
                  and then R (A'First) = F (A (A'First), Init));
               pragma Loop_Invariant
                 (for all K in A'First .. I =>
                    (if K > A'First then
                         Ind_Prop (A, R (K - 1), K)
                     and then R (K) = F (A (K), R (K - 1))));
               pragma Loop_Invariant
                    (if I = A'First then Acc = Init else Acc = R (I - 1));
               if I /= A'Last then
                  Prove_Ind (A, Acc, I);
               else
                  Prove_Last (A, Acc);
               end if;
               Acc := R (I);
            end loop;
         end return;
      end Fold;

      ---------------
      -- Prove_Ind --
      ---------------

      procedure Prove_Ind  (A : Array_Type; X : Element_Out; I : Index_Type) is
      null;

      ----------------
      -- Prove_Last --
      ----------------

      procedure Prove_Last  (A : Array_Type; X : Element_Out) is null;

   end Fold_Left_Acc;

   -----------------
   -- Fold_Left_I --
   -----------------

   package body Fold_Left_I is

      ----------
      -- Fold --
      ----------

      function Fold (A : Array_Type; Init : Element_Out) return Element_Out
        with SPARK_Mode =>
#if SPARK_BODY_MODE="On"
          On
#else
          Off
#end if;
      is
      begin
         return R : Element_Out := Init do
            for I in A'Range loop
               pragma Loop_Invariant
                 (Ind_Prop (A, R, I)
                  and then F (A (I), I, R) = Acc.Fold (A, Init) (I));
               if I /= A'Last then
                  Acc.Prove_Ind (A, R, I);
               end if;
               R := F (A (I), I, R);
            end loop;
         end return;
      end Fold;
   end Fold_Left_I;

   ---------------------
   -- Fold_Left_I_Acc --
   ---------------------

   package body Fold_Left_I_Acc is

      ----------
      -- Fold --
      ----------

      function Fold (A : Array_Type; Init : Element_Out) return Acc_Array
        with SPARK_Mode =>
#if SPARK_BODY_MODE="On"
          On
#else
          Off
#end if;
      is
         Acc : Element_Out := Init;
      begin
         return R : Acc_Array (A'First .. A'Last) := (others => Init) do
            for I in A'Range loop
               pragma Assert (Ind_Prop (A, Acc, I));
               R (I) := F (A (I), I, Acc);
               pragma Loop_Invariant
                 (Ind_Prop (A, Init, A'First)
                  and then R (A'First) = F (A (A'First), A'First, Init));
               pragma Loop_Invariant
                 (for all K in A'First .. I =>
                    (if K > A'First then
                         Ind_Prop (A, R (K - 1), K)
                     and then R (K) = F (A (K), K, R (K - 1))));
               pragma Loop_Invariant
                    (if I = A'First then Acc = Init else Acc = R (I - 1));
               if I /= A'Last then
                  Prove_Ind (A, Acc, I);
               else
                  Prove_Last (A, Acc);
               end if;
               Acc := R (I);
            end loop;
         end return;
      end Fold;

      ---------------
      -- Prove_Ind --
      ---------------

      procedure Prove_Ind  (A : Array_Type; X : Element_Out; I : Index_Type) is
      null;

      ----------------
      -- Prove_Last --
      ----------------

      procedure Prove_Last  (A : Array_Type; X : Element_Out) is null;

   end Fold_Left_I_Acc;

   ----------------
   -- Fold_Right --
   ----------------

   package body Fold_Right is

      ----------
      -- Fold --
      ----------

      function Fold (A : Array_Type; Init : Element_Out) return Element_Out
        with SPARK_Mode =>
#if SPARK_BODY_MODE="On"
          On
#else
          Off
#end if;
      is
      begin
         return R : Element_Out := Init do
            for I in reverse A'Range loop
               pragma Loop_Invariant
                 (Ind_Prop (A, R, I)
                  and then F (A (I), R) = Acc.Fold (A, Init) (I));
               if I /= A'First then
                  Acc.Prove_Ind (A, R, I);
               end if;
               R := F (A (I), R);
            end loop;
         end return;
      end Fold;
   end Fold_Right;

   --------------------
   -- Fold_Right_Acc --
   --------------------

   package body Fold_Right_Acc is

      ----------
      -- Fold --
      ----------

      function Fold (A : Array_Type; Init : Element_Out) return Acc_Array
        with SPARK_Mode =>
#if SPARK_BODY_MODE="On"
          On
#else
          Off
#end if;
      is
         Acc : Element_Out := Init;
      begin
         return R : Acc_Array (A'First .. A'Last) := (others => Init) do
            for I in reverse A'Range loop
               pragma Assert (Ind_Prop (A, Acc, I));
               R (I) := F (A (I), Acc);
               pragma Loop_Invariant
                 (Ind_Prop (A, Init, A'Last)
                  and then R (A'Last) = F (A (A'Last), Init));
               pragma Loop_Invariant
                 (for all K in I .. A'Last =>
                    (if K < A'Last then
                         Ind_Prop (A, R (K + 1), K)
                     and then R (K) = F (A (K), R (K + 1))));
               pragma Loop_Invariant
                    (if I = A'Last then Acc = Init else Acc = R (I + 1));
               if I /= A'First then
                  Prove_Ind (A, Acc, I);
               else
                  Prove_Last (A, Acc);
               end if;
               Acc := R (I);
            end loop;
         end return;
      end Fold;

      ---------------
      -- Prove_Ind --
      ---------------

      procedure Prove_Ind (A : Array_Type; X : Element_Out; I : Index_Type) is
      null;

      ----------------
      -- Prove_Last --
      ----------------

      procedure Prove_Last  (A : Array_Type; X : Element_Out) is null;

   end Fold_Right_Acc;

   ---------
   -- Sum --
   ---------

   package body Sum is

      -------------
      -- Sum_Cst --
      -------------

      procedure Sum_Cst (A : Array_Type; C : Element_Out) with SPARK_Mode =>
#if SPARK_BODY_MODE="On"
          On
#else
          Off
#end if;
      is
      begin
         for I in A'Range loop
            if Value (A (I)) /= C then
               return;
            end if;
            pragma Loop_Invariant
              (Sum_Left.Acc.Fold (A, 0) (I) =
                   C * Element_Out'Base (I - A'First) + C);
            pragma Loop_Invariant
              (for all K in A'First .. I => Value (A (K)) = C);
         end loop;
      end Sum_Cst;

      ----------------
      -- Update_Sum --
      ----------------

      procedure Update_Sum (A1, A2 : Array_Type; I : Index_Type) with
        SPARK_Mode =>
#if SPARK_BODY_MODE="On"
          On
#else
          Off
#end if;
      is
         function In_Range (A : Array_Type; K : Index_Type) return Boolean is
           (if K < I then
               Sum_Left.Acc.Fold (A, 0) (K) in
                Element_Out'First * (Element_Out'Base (K - A'First) + 1)
            .. Element_Out'Last * (Element_Out'Base (K - A'First) + 1)
            else Sum_Left.Acc.Fold (A, 0) (K) in
               Value (A (I)) +
              Element_Out'First * Element_Out'Base (K - A'First)
            .. Value (A (I)) +
              Element_Out'Last * Element_Out'Base (K - A'First))
         with
           Pre => K in A'Range and then I in A'Range,
           Post =>
             (if In_Range'Result then
                (if K > I then
                   (if Value (A (I)) >= 0 then
                        Sum_Left.Acc.Fold (A, 0) (K) >=
                        Element_Out'Base'First + Value (A (I))
                      else
                        Sum_Left.Acc.Fold (A, 0) (K) <=
                        Element_Out'Base'Last + Value (A (I)))));
         --  If I has already been encountered, it is safe to subtract
         --  Value (A (I)) from Sum_Left.Acc.Fold (A, 0) (K).

         procedure In_Range_Ind (A : Array_Type; K : Index_Type)
         with
           Pre  => K in A'Range and then I in A'Range and then In_Range (A, K),
           Post => (if K < A'Last then In_Range (A, K + 1));
         --  In_Range is inductive

         ------------------
         -- In_Range_Ind --
         ------------------

         procedure In_Range_Ind (A : Array_Type; K : Index_Type) is
            null;

      begin
         for K in A1'Range loop
            pragma Loop_Invariant (In_Range (A1, K));
            pragma Loop_Invariant (In_Range (A2, K));
            pragma Loop_Invariant
              (if K < I then
                    Sum_Left.Acc.Fold (A1, 0) (K) =
                    Sum_Left.Acc.Fold (A2, 0) (K)
               else
                    Sum_Left.Acc.Fold (A1, 0) (K) - Value (A1 (I)) =
                    Sum_Left.Acc.Fold (A2, 0) (K) - Value (A2 (I)));
         end loop;

         pragma Assert
           (Sum_Left.Acc.Fold (A1, 0) (A1'Last) - Value (A1 (I)) =
            Sum_Left.Acc.Fold (A2, 0) (A1'Last) - Value (A2 (I)));
      end Update_Sum;

   end Sum;

   -----------
   -- Sum_2 --
   -----------

   package body Sum_2 is

      -------------
      -- Sum_Cst --
      -------------

      procedure Sum_Cst (A : Array_Type; C : Element_Out) with SPARK_Mode =>
#if SPARK_BODY_MODE="On"
          On
#else
          Off
#end if;
      is
         function Sum_Cst (I : Index_1; J : Index_2) return Boolean is
           (Fold_Sum.Acc.Fold (A, 0) (I, J) =
                C * (Element_Out'Base (I - A'First (1)) * A'Length (2) +
                      Element_Out'Base (J - A'First (2))) + C)
          with Pre => I in A'Range (1) and then J in A'Range (2);
         --  The property we want to show at position I, J

         procedure Prove_First_Col (I : Index_1) with
           Pre  => A'Length (2) > 0 and then I in A'Range (1) and then
           (I = A'First (1) or else Sum_Cst (I - 1, A'Last (2))),
           Post =>
             (if Value (A (I, A'First (2))) = C then
                Sum_Cst (I, A'First (2)));
         --  Prove the first iteration of the inner loop

         procedure Prove_Last with
           Pre  => (if A'Length (1) > 0 and then A'Length (2) > 0 then
                    Sum_Cst (A'Last (1), A'Last (2))),
           Post => Sum (A) = C * A'Length (1) * A'Length (2);
         --  Prove the postcondition

         procedure Prove_Next_Col (I : Index_1; J : Index_2) with
           Pre  => I in A'Range (1) and then J in A'Range (2) and then
           (J = A'First (2) or else Sum_Cst (I, J - 1)),
           Post =>
             (if J /= A'First (2) and then Value (A (I, J)) = C then
                Sum_Cst (I, J));
         --  Prove the next iteration of the inner loop

         ---------------------
         -- Prove_First_Col --
         ---------------------

         procedure Prove_First_Col (I : Index_1) is null;

         ----------------
         -- Prove_Last --
         ----------------

         procedure Prove_Last is null;

         --------------------
         -- Prove_Next_Col --
         --------------------

         procedure Prove_Next_Col (I : Index_1; J : Index_2) is null;

      begin
         if A'Length (2) > 0 then
            for I in A'Range (1) loop
               pragma Loop_Invariant
                 (I = A'First (1) or else
                  (for all K in A'First (1) .. I - 1 =>
                       (for all L in A'Range (2) => Value (A (K, L)) = C)));
               pragma Loop_Invariant
                 (I = A'First (1) or else Sum_Cst (I - 1, A'Last (2)));
               Prove_First_Col (I);
               for J in A'Range (2) loop
                  if Value (A (I, J)) /= C then
                     return;
                  end if;
                  Prove_Next_Col (I, J);
                  pragma Loop_Invariant (Sum_Cst (I, J));
                  pragma Loop_Invariant
                    (for all L in A'First (2) .. J => Value (A (I, L)) = C);
               end loop;
            end loop;
         end if;
         Prove_Last;
      end Sum_Cst;

      ----------------
      -- Update_Sum --
      ----------------

      procedure Update_Sum (A1, A2 : Array_Type; I : Index_1; J : Index_2) with
        SPARK_Mode =>
#if SPARK_BODY_MODE="On"
          On
#else
          Off
#end if;
      is

         function In_Range
           (A : Array_Type; K : Index_1; L : Index_2) return Boolean
         is
           (if K < I or else (K = I and then L < J) then
                 Fold_Sum.Acc.Fold (A, 0) (K, L) in
               Element_Out'First *
              (Element_Out'Base (K - A'First (1)) * A'Length (2)
               + Element_Out'Base (L - A'First (2)) + 1)
            .. Element_Out'Last *
              (Element_Out'Base (K - A'First (1)) * A'Length (2)
               + Element_Out'Base (L - A'First (2)) + 1)
            else Fold_Sum.Acc.Fold (A, 0) (K, L) in
               Value (A (I, J)) + Element_Out'First *
            (Element_Out'Base (K - A'First (1)) * A'Length (2)
             + Element_Out'Base (L - A'First (2)))
            .. Value (A (I, J)) + Element_Out'Last *
            (Element_Out'Base (K - A'First (1)) * A'Length (2)
             + Element_Out'Base (L - A'First (2))))
         with
           Pre => K in A'Range (1) and then L in A'Range (2)
           and then I in A'Range (1) and then J in A'Range (2),
           Post =>
             (if In_Range'Result then
                (if K > I  or else (K = I and then L >= J) then
                   (if Value (A (I, J)) >= 0 then
                        Fold_Sum.Acc.Fold (A, 0) (K, L) >=
                        Element_Out'Base'First + Value (A (I, J))
                      else
                        Fold_Sum.Acc.Fold (A, 0) (K, L) <=
                        Element_Out'Base'Last + Value (A (I, J)))));
         --  If (I, J) has already been encountered, it is safe to subtract
         --  A (I, J) from Fold_Sum.Acc.Fold (A, 0) (K, L).

         function Update_Sum (K : Index_1; L : Index_2) return Boolean is
           (if K < I or else (K = I and then L < J) then
                 Fold_Sum.Acc.Fold (A1, 0) (K, L) =
                Fold_Sum.Acc.Fold (A2, 0) (K, L)
            else
               Fold_Sum.Acc.Fold (A1, 0) (K, L) -
                Value (A1 (I, J)) =
              Fold_Sum.Acc.Fold (A2, 0) (K, L) -
                Value (A2 (I, J)))
          with Pre => K in A1'Range (1) and then L in A1'Range (2)
           and then I in A1'Range (1) and then J in A1'Range (2)
           and then A1'First (1) = A2'First (1)
           and then A1'Last (1) = A2'Last (1)
           and then A1'First (2) = A2'First (2)
           and then A1'Last (2) = A2'Last (2)
           and then In_Range (A1, K, L) and then In_Range (A2, K, L);
         --  The property we want to show at position I, J

         procedure In_Range_Ind (A : Array_Type; K : Index_1; L : Index_2)
         with
           Pre  => K in A'Range (1) and then L in A'Range (2)
           and then I in A'Range (1) and then J in A'Range (2)
           and then In_Range (A, K, L),
           Post =>
             (if L < A'Last (2) then In_Range (A, K, L + 1)
              elsif K < A'Last (1) then In_Range (A, K + 1, A'First (2)));
         --  In_Range is inductive

         procedure Prove_Next_Col (K : Index_1; L : Index_2) with
           Pre => K in A1'Range (1) and then L in A1'Range (2)
           and then I in A1'Range (1) and then J in A1'Range (2)
           and then A1'First (1) = A2'First (1)
           and then A1'Last (1) = A2'Last (1)
           and then A1'First (2) = A2'First (2)
           and then A1'Last (2) = A2'Last (2)
           and then In_Range (A1, K, L) and then In_Range (A2, K, L)
           and then (if K /= I or else L /= J then
                       Value (A1 (K, L)) = Value (A2 (K, L)))
           and then
             (L = A1'First (2) or else
                (In_Range (A1, K, L - 1) and then In_Range (A2, K, L - 1)
                 and then Update_Sum (K, L - 1))),
           Post => L = A1'First (2) or else Update_Sum (K, L);
         --  Prove the next iteration of the inner loop

         ------------------
         -- In_Range_Ind --
         ------------------

         procedure In_Range_Ind (A : Array_Type; K : Index_1; L : Index_2) is
         null;

         --------------------
         -- Prove_Next_Col --
         --------------------

         procedure Prove_Next_Col (K : Index_1; L : Index_2) is
         begin
            if L = A1'First (2) then
               return;
            else
               pragma Assert
                 (Fold_Sum.Acc.Fold (A1, 0) (K, L) =
                    Fold_Sum.Acc.Fold (A1, 0) (K, L - 1) + Value (A1 (K, L)));
               pragma Assert
                 (Fold_Sum.Acc.Fold (A2, 0) (K, L) =
                    Fold_Sum.Acc.Fold (A2, 0) (K, L - 1) + Value (A2 (K, L)));
               if K < I or else (K = I and then L < J) then
                  pragma Assert (Fold_Sum.Acc.Fold (A1, 0) (K, L) =
                                   Fold_Sum.Acc.Fold (A2, 0) (K, L));
               else
                  pragma Assert
                    (Fold_Sum.Acc.Fold (A1, 0) (K, L) - Value (A1 (I, J)) =
                         Fold_Sum.Acc.Fold (A2, 0) (K, L) - Value (A2 (I, J)));
               end if;
            end if;
         end Prove_Next_Col;

      begin
         for K in A1'Range (1) loop
            pragma Loop_Invariant (In_Range (A1, K, A1'First (2)));
            pragma Loop_Invariant (In_Range (A2, K, A2'First (2)));
            pragma Loop_Invariant
              (if K < I  or else (K = I and then A1'First (2) < J) then
                    Fold_Sum.Acc.Fold (A1, 0) (K, A1'First (2)) =
                    Fold_Sum.Acc.Fold (A2, 0) (K, A1'First (2))
               else
                    Fold_Sum.Acc.Fold (A1, 0) (K, A1'First (2)) -
                       Value (A1 (I, J)) =
                    Fold_Sum.Acc.Fold (A2, 0) (K, A1'First (2)) -
                       Value (A2 (I, J)));
            for L in A1'Range (2) loop
               pragma Loop_Invariant (In_Range (A1, K, L));
               pragma Loop_Invariant (In_Range (A2, K, L));
               pragma Loop_Invariant
                 (if K < I or else (K = I and then L < J) then
                       Fold_Sum.Acc.Fold (A1, 0) (K, L) =
                       Fold_Sum.Acc.Fold (A2, 0) (K, L)
                  else
                       Fold_Sum.Acc.Fold (A1, 0) (K, L) -
                         Value (A1 (I, J)) =
                       Fold_Sum.Acc.Fold (A2, 0) (K, L) -
                         Value (A2 (I, J)));
               In_Range_Ind (A1, K, L);
               In_Range_Ind (A2, K, L);
               if L /= A1'Last (2) then
                  Prove_Next_Col (K, L + 1);
               end if;
            end loop;
         end loop;

         pragma Assert
           (Fold_Sum.Acc.Fold (A1, 0) (A1'Last (1), A1'Last (2)) -
                         Value (A1 (I, J)) =
            Fold_Sum.Acc.Fold (A2, 0) (A1'Last (1), A1'Last (2)) -
                         Value (A2 (I, J)));
      end Update_Sum;

   end Sum_2;

end SPARK.Higher_Order.Fold;
