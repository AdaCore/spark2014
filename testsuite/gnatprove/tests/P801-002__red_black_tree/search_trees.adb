package body Search_Trees with SPARK_Mode is

   function Values (T : Search_Tree) return Value_Set with
     Refined_Post =>
       (if Size (T.Struct) = 0 then Is_Empty (Values'Result)
        else
          ((for all I in Index_Type =>
             (if Model (T.Struct, T.Root) (I).K then Mem (Values'Result, T.Values (I))))
           and then
             (for all V in Natural =>
                  (if Mem (Values'Result, V) then
                     (for some I in Index_Type =>
                            Model (T.Struct, T.Root) (I).K and then T.Values (I) = V)))))
   is
      S : Value_Set;
   begin
      if T.Root = 0 then
         return S;
      end if;

      for J in Index_Type loop
         if Model (T.Struct, T.Root) (J).K
           and then not Mem (S, T.Values (J))
         then
            S := Add (S, T.Values (J));
         end if;
         pragma Loop_Invariant (Length (S) <= J);
         pragma Loop_Invariant
           (for all I in 1 .. J =>
              (if Model (T.Struct, T.Root) (I).K then Mem (S, T.Values (I))));
         pragma Loop_Invariant
           (for all V in Natural =>
              (if Mem (S, V) then
                   (for some I in Index_Type =>
                        Model (T.Struct, T.Root) (I).K and then T.Values (I) = V)));
      end loop;
      return S;
   end Values;

   function Ordered_Leafs (F : Forest; Root : Index_Type; Values : Value_Array) return Boolean is
     (for all I in Index_Type =>
        (for all J in Index_Type =>
             (if Model (F, Root) (I).K
              and then Model (F, Root) (J).K
              and then Model (F, Root) (I).A < Model (F, Root) (J).A
              then (if Get (Model (F, Root) (J).A,
                            Length (Model (F, Root) (I).A) + 1)
                    = Left
                    then
                       Values (J) < Values (I)
                    else Values (J) > Values (I)))));

   function Find_Root (F : Forest; Root, I, J : Index_Type) return Index_Type with
     Ghost,
     Pre  => Valid_Root (F, Root)
     and then Model (F, Root) (I).K and then Model (F, Root) (J).K,
     Post => Model (F, Root) (Find_Root'Result).K
     and Model (F, Root) (Find_Root'Result).A <= Model (F, Root) (I).A
     and Model (F, Root) (Find_Root'Result).A <= Model (F, Root) (J).A
     and (I = Find_Root'Result or else J = Find_Root'Result
          or else Get (Model (F, Root) (I).A, Length (Model (F, Root) (Find_Root'Result).A) + 1)
            /= Get (Model (F, Root) (J).A, Length (Model (F, Root) (Find_Root'Result).A) + 1));

   function Find_Root (F : Forest; Root, I, J : Index_Type) return Index_Type is
      M  : constant Model_Type := Model (F, Root);
      KI : Index_Type := I;
      KJ : Index_Type := J;
   begin
      while KI /= KJ loop
         pragma Loop_Invariant (M (KI).A <= M (I).A);
         pragma Loop_Invariant (M (KI).K);
         pragma Loop_Invariant (M (KJ).A <= M (J).A);
         pragma Loop_Invariant (M (KJ).K);
         pragma Loop_Invariant
           (if Length (M (KI).A) > Length (M (KJ).A) then KJ = J);
         pragma Loop_Invariant
           (if Length (M (KJ).A) > Length (M (KI).A) then KI = I);
         if Length (M (KI).A) > Length (M (KJ).A) then
            KI := Parent (F, KI);
         elsif Length (M (KJ).A) > Length (M (KI).A) then
            KJ := Parent (F, KJ);
         else
            KI := Parent (F, KI);
            KJ := Parent (F, KJ);
         end if;
      end loop;
      return KI;
   end Find_Root;

   procedure Prove_Extract_Order
     (F, F_Old : Forest; Root, V : Index_Type; Values : Value_Array)
     with Ghost,
     Pre => Valid_Root (F_Old, Root) and then Valid_Root (F, Root)
     and then Valid_Root (F, V) and then not Valid_Root (F_Old, V)
     and then Model (F_Old, Root) (V).K
     and then Ordered_Leafs (F_Old, Root, Values)
     and then
       (for all I in Index_Type =>
          (if Model (F_Old, Root) (I).K then
               (if Model (F_Old, Root) (V).A <= Model (F_Old, Root) (I).A
                then Model (F, V) (I).K
                else Model (F, Root) (I).K)))
     and then
       (for all I in Index_Type =>
          (if Model (F, Root) (I).K then Model (F_Old, Root) (I).K))
     and then
       (for all I in Index_Type =>
          (if V /= 0 and then Model (F, V) (I).K then Model (F_Old, Root) (I).K))
     and then
       (for all I in Index_Type =>
          (if Model (F, Root) (I).K then Model (F, Root) (I).A = Model (F_Old, Root) (I).A))
     and then
       (for all I in Index_Type =>
          (if V /= 0 and then Model (F, V) (I).K then
               Is_Concat (Model (F_Old, Root) (V).A, Model (F, V) (I).A, Model (F_Old, Root) (I).A))),
     Post => Ordered_Leafs (F, Root, Values)
     and then Ordered_Leafs (F, V, Values)
     and then
       (for all I in Index_Type =>
          (if Model (F, Root) (I).K
           and Model (F, Root) (I).A < Model (F_Old, Root) (V).A then
               (if Get (Model (F_Old, Root) (V).A,
                        Length (Model (F, Root) (I).A) + 1) = Left
                  then
                    (for all J in Index_Type =>
                       (if Model (F, V) (J).K
                            then Values (J) < Values (I)))
                    else
                  (for all J in Index_Type =>
                     (if Model (F, V) (J).K
                          then Values (J) > Values (I))))))
   is
   begin
      for I in Index_Type loop
         pragma Loop_Invariant
           (for all K in 1 .. I - 1 =>
              (for all J in Index_Type =>
                   (if Model (F, Root) (K).K
                    and then Model (F, Root) (J).K
                    and then Model (F, Root) (K).A < Model (F, Root) (J).A
                    then (if Get (Model (F, Root) (J).A,
                      Length (Model (F, Root) (K).A) + 1)
                      = Left
                      then
                         Values (J) < Values (K)
                      else Values (J) > Values (K)))));

         for J in Index_Type loop
            if Model (F, Root) (I).K
              and then Model (F, Root) (J).K
              and then Model (F, Root) (I).A < Model (F, Root) (J).A
            then
               pragma Assert (Model (F_Old, Root) (I).A < Model (F_Old, Root) (J).A);
               pragma Assert
                 (if Get (Model (F, Root) (J).A,
                  Length (Model (F, Root) (I).A) + 1)
                  = Left
                  then Values (J) < Values (I)
                  else Values (J) > Values (I));
            end if;
            pragma Loop_Invariant
              (for all K in 1 .. J =>
                 (if Model (F, Root) (I).K
                  and then Model (F, Root) (K).K
                  and then Model (F, Root) (I).A < Model (F, Root) (K).A
                  then (if Get (Model (F, Root) (K).A,
                    Length (Model (F, Root) (I).A) + 1)
                    = Left
                    then
                       Values (K) < Values (I)
                    else Values (K) > Values (I))));
         end loop;
      end loop;
      pragma Assert
        (for all K in Index_Type =>
           (for all J in Index_Type =>
                (if Model (F, Root) (K).K
                 and then Model (F, Root) (J).K
                 and then Model (F, Root) (K).A < Model (F, Root) (J).A
                 then (if Get (Model (F, Root) (J).A,
                   Length (Model (F, Root) (K).A) + 1)
                   = Left
                   then
                      Values (J) < Values (K)
                   else Values (J) > Values (K)))));
      pragma Assert (Ordered_Leafs (F, Root, Values));

      for I in Index_Type loop
         pragma Loop_Invariant
           (for all K in 1 .. I - 1 =>
              (for all J in Index_Type =>
                   (if Model (F, V) (K).K
                    and then Model (F, V) (J).K
                    and then Model (F, V) (K).A < Model (F, V) (J).A
                    then (if Get (Model (F, V) (J).A,
                      Length (Model (F, V) (K).A) + 1)
                      = Left
                      then
                         Values (J) < Values (K)
                      else Values (J) > Values (K)))));

         for J in Index_Type loop
            if Model (F, V) (I).K
              and then Model (F, V) (J).K
              and then Model (F, V) (I).A < Model (F, V) (J).A
            then
               pragma Assert (Model (F_Old, Root) (I).A < Model (F_Old, Root) (J).A);
               pragma Assert
                 (if Get (Model (F, V) (J).A,
                  Length (Model (F, V) (I).A) + 1)
                  = Left
                  then Values (J) < Values (I)
                  else Values (J) > Values (I));
            end if;
            pragma Loop_Invariant
              (for all K in 1 .. J =>
                 (if Model (F, V) (I).K
                  and then Model (F, V) (K).K
                  and then Model (F, V) (I).A < Model (F, V) (K).A
                  then (if Get (Model (F, V) (K).A,
                    Length (Model (F, V) (I).A) + 1)
                    = Left
                    then
                       Values (K) < Values (I)
                    else Values (K) > Values (I))));
         end loop;
      end loop;
      pragma Assert
        (for all K in Index_Type =>
           (for all J in Index_Type =>
                (if Model (F, V) (K).K
                 and then Model (F, V) (J).K
                 and then Model (F, V) (K).A < Model (F, V) (J).A
                 then (if Get (Model (F, V) (J).A,
                   Length (Model (F, V) (K).A) + 1)
                   = Left
                   then
                      Values (J) < Values (K)
                   else Values (J) > Values (K)))));
      pragma Assert (Ordered_Leafs (F, V, Values));
   end Prove_Extract_Order;

   procedure Prove_Plug_Order
     (F, F_Old : Forest; Root, V : Index_Type; Values : Value_Array)
     with Ghost,
     Pre => Valid_Root (F_Old, Root) and then Valid_Root (F, Root)
     and then Valid_Root (F_Old, V) and then not Valid_Root (F, V)
     and then Model (F, Root) (V).K
     and then Ordered_Leafs (F_Old, Root, Values)
     and then Ordered_Leafs (F_Old, V, Values)
     and then
       (for all I in Index_Type =>
          (if Model (F_Old, Root) (I).K
           and Model (F_Old, Root) (I).A < Model (F, Root) (V).A then
               (if Get (Model (F, Root) (V).A,
                        Length (Model (F_Old, Root) (I).A) + 1) = Left
                  then
                    (for all J in Index_Type =>
                       (if Model (F_Old, V) (J).K
                            then Values (J) < Values (I)))
                    else
                  (for all J in Index_Type =>
                     (if Model (F_Old, V) (J).K
                          then Values (J) > Values (I))))))
     and then
       (for all I in Index_Type =>
          (if Model (F, Root) (I).K then
               (if Model (F, Root) (V).A <= Model (F, Root) (I).A
                then Model (F_Old, V) (I).K
                else Model (F_Old, Root) (I).K)))
     and then
       (for all I in Index_Type =>
          (if Model (F_Old, Root) (I).K then Model (F, Root) (I).K))
     and then
       (for all I in Index_Type =>
          (if V /= 0 and then Model (F_Old, V) (I).K then Model (F, Root) (I).K))
     and then
       (for all I in Index_Type =>
          (if Model (F_Old, Root) (I).K then Model (F_Old, Root) (I).A = Model (F, Root) (I).A))
     and then
       (for all I in Index_Type =>
          (if V /= 0 and then Model (F_Old, V) (I).K then
               Is_Concat (Model (F, Root) (V).A, Model (F_Old, V) (I).A, Model (F, Root) (I).A))),
     Post => Ordered_Leafs (F, Root, Values)
   is
   begin
      for I in Index_Type loop
         pragma Loop_Invariant
           (for all K in 1 .. I - 1 =>
              (for all J in Index_Type =>
                   (if Model (F, Root) (K).K
                    and then Model (F, Root) (J).K
                    and then Model (F, Root) (K).A < Model (F, Root) (J).A
                    then (if Get (Model (F, Root) (J).A,
                      Length (Model (F, Root) (K).A) + 1)
                      = Left
                      then
                         Values (J) < Values (K)
                      else Values (J) > Values (K)))));

         for J in Index_Type loop
            if Model (F_Old, Root) (I).K
              and then Model (F_Old, Root) (J).K
              and then Model (F, Root) (I).A < Model (F, Root) (J).A
            then
               pragma Assert (Model (F_Old, Root) (I).A < Model (F_Old, Root) (J).A);
               pragma Assert
                 (if Get (Model (F, Root) (J).A,
                  Length (Model (F, Root) (I).A) + 1)
                  = Left
                  then Values (J) < Values (I)
                  else Values (J) > Values (I));
            end if;
            if Model (F_Old, V) (I).K
              and then Model (F_Old, V) (J).K
              and then Model (F, Root) (I).A < Model (F, Root) (J).A
            then
               pragma Assert (Model (F_Old, V) (I).A < Model (F_Old, V) (J).A);
               pragma Assert (Get (Model (F, Root) (J).A,
                              Length (Model (F, Root) (I).A) + 1)
                              = Get (Model (F_Old, V) (J).A,
                                Length (Model (F_Old, V) (I).A) + 1));
               pragma Assert
                 (if Get (Model (F, Root) (J).A,
                  Length (Model (F, Root) (I).A) + 1)
                  = Left
                  then Values (J) < Values (I)
                  else Values (J) > Values (I));
            end if;
            if Model (F_Old, Root) (I).K
              and then Model (F_Old, V) (J).K
              and then Model (F, Root) (I).A < Model (F, Root) (J).A
            then
               pragma Assert (Model (F, Root) (V).A <= Model (F, Root) (J).A);
               Prove_Model_Distinct (F_Old, Root, V);
               pragma Assert (Model (F_Old, Root) (I).A < Model (F, Root) (V).A);
               pragma Assert
                 (Get (Model (F, Root) (V).A, Length (Model (F, Root) (I).A) + 1)
                    = Get (Model (F, Root) (V).A, Length (Model (F, Root) (I).A) + 1));
               pragma Assert
                 (if Get (Model (F, Root) (J).A,
                  Length (Model (F, Root) (I).A) + 1)
                  = Left
                  then Values (J) < Values (I)
                  else Values (J) > Values (I));
            end if;
            if Model (F_Old, V) (I).K
              and then Model (F_Old, Root) (J).K
            then
               Prove_Model_Distinct (F_Old, Root, V);
               pragma Assert (not (Model (F, Root) (I).A < Model (F, Root) (J).A));
            end if;
            pragma Loop_Invariant
              (for all K in 1 .. J =>
                 (if Model (F, Root) (I).K
                  and then Model (F, Root) (K).K
                  and then Model (F, Root) (I).A < Model (F, Root) (K).A
                  then (if Get (Model (F, Root) (K).A,
                    Length (Model (F, Root) (I).A) + 1)
                    = Left
                    then
                       Values (K) < Values (I)
                    else Values (K) > Values (I))));
         end loop;
      end loop;
      pragma Assert
        (for all I in Index_Type =>
           (for all J in Index_Type =>
                (if Model (F, Root) (I).K
                 and then Model (F, Root) (J).K
                 and then Model (F, Root) (I).A < Model (F, Root) (J).A
                 then (if Get (Model (F, Root) (J).A,
                   Length (Model (F, Root) (I).A) + 1)
                   = Left
                   then
                      Values (J) < Values (I)
                   else Values (J) > Values (I)))));
   end Prove_Plug_Order;

   procedure Prove_Preserved_Order
     (F1, F2 : Forest; Root : Index_Type; Values : Value_Array)
     with Ghost,
     Pre => Valid_Root (F1, Root) and then Valid_Root (F2, Root)
     and then Ordered_Leafs (F2, Root, Values)
     and then Model (F2, Root) = Model (F1, Root),
     Post => Ordered_Leafs (F1, Root, Values)
   is
   begin
      pragma Assert
        (for all I in Index_Type =>
           (for all J in Index_Type =>
                (if Model (F1, Root) (I).K
                 and then Model (F1, Root) (J).K
                 and then Model (F1, Root) (I).A < Model (F1, Root) (J).A
                 then Model (F2, Root) (I).K
                   and then Model (F2, Root) (J).K
                   and then Model (F2, Root) (I).A < Model (F2, Root) (J).A
                   and then Get (Model (F1, Root) (J).A, Length (Model (F1, Root) (I).A) + 1)
                     = Get (Model (F2, Root) (J).A, Length (Model (F2, Root) (I).A) + 1))));
      pragma Assert
        (for all I in Index_Type =>
           (for all J in Index_Type =>
                (if Model (F1, Root) (I).K
                 and then Model (F1, Root) (J).K
                 and then Model (F1, Root) (I).A < Model (F1, Root) (J).A
                 then (if Get (Model (F1, Root) (J).A,
                   Length (Model (F1, Root) (I).A) + 1)
                   = Left
                   then
                      Values (J) < Values (I)
                   else Values (J) > Values (I)))));
   end Prove_Preserved_Order;

   procedure Prove_Preserved_Values (T1, T2 : Search_Tree) with
     Ghost,
     Pre  => T1.Root /= 0 and then Valid_Root (T1.Struct, T1.Root)
     and then T2.Root /= 0 and then Valid_Root (T2.Struct, T2.Root)
     and then Ordered_Leafs (T1.Struct, T1.Root, T1.Values)
     and then Ordered_Leafs (T2.Struct, T2.Root, T2.Values)
     and then (for all I in Index_Type =>
                 (if Model (T1.Struct, T1.Root) (I).K
                  then Model (T2.Struct, T2.Root) (I).K))
     and then (for all I in Index_Type =>
                 (if Model (T2.Struct, T2.Root) (I).K
                  then Model (T1.Struct, T1.Root) (I).K))
     and then T1.Values = T2.Values,
     Post => Values (T1) = Values (T2)
   is
   begin
      null;
   end Prove_Preserved_Values;

   procedure Prove_Order_Total (T : Search_Tree; L : Index_Type; V : Natural) with
     Ghost,
     Pre  => Size (T.Struct) > 0 and then T.Root > 0
     and then Valid_Root (T.Struct, T.Root)
     and then Ordered_Leafs (T.Struct, T.Root, T.Values)
     and then T.Values (L) /= V
     and then Model (T.Struct, T.Root) (L).K
     and then
       (if V < T.Values (L) then Peek (T.Struct, L, Left) = 0
        else Peek (T.Struct, L, Right) = 0)
     and then
       (for all I in Index_Type =>
          (if Model (T.Struct, T.Root) (I).K then
               (if Model (T.Struct, T.Root) (I).A < Model (T.Struct, T.Root) (L).A
                      then (if Get (Model (T.Struct, T.Root) (L).A, Length (Model (T.Struct, T.Root) (I).A) + 1) = Left then
                              V < T.Values (I)
                              else V > T.Values (I))))),
     Post =>
       (for all I in Index_Type =>
          (if Model (T.Struct, T.Root) (I).K then T.Values (I) /= V))
   is
   begin
      pragma Assert
        (for all I in Index_Type =>
           (if Model (T.Struct, T.Root) (I).K
            then Model (T.Struct, T.Root) (Find_Root (T.Struct, T.Root, I, L)).K));
      if V < T.Values (L) then
         Prove_Model_Total (T.Struct, T.Root, L, Left);
      else
         Prove_Model_Total (T.Struct, T.Root, L, Right);
      end if;
      pragma Assert
        (for all I in Index_Type =>
           (if Model (T.Struct, T.Root) (I).K
            and then Find_Root (T.Struct, T.Root, I, L) = L
            then T.Values (I) /= V));
   end Prove_Order_Total;

   procedure Left_Rotate (T : in out Search_Tree; I : Index_Type) is
      X, Y    : Index_Type;
      YL      : Extended_Index_Type;
      Is_Root : constant Boolean := I = T.Root;
      J       : Index_Type := 1;
      D       : Direction := Left;
      T_Old   : Search_Tree := T with Ghost;
      F_Old   : Forest := T.Struct with Ghost;
      F_1, F_2, F_3, F_4, F_5 : Forest := T.Struct with Ghost;

      procedure Prove_Extract_X with Ghost is
      begin
         if not Is_Root then
            Prove_Extract_Order (T.Struct, F_Old, T.Root, X, T.Values);
         end if;
         F_1 := T.Struct;
      end Prove_Extract_X;

      procedure Prove_Extract_Y with Ghost is
      begin
         Prove_Extract_Order (T.Struct, F_1, X, Y, T.Values);
         pragma Assert (Get (Model (F_1, X) (Y).A, 1) = Right);
         pragma Assert (T.Values (X) < T.Values (Y));
         if not Is_Root then
            Prove_Preserved_Order (T.Struct, F_1, T.Root, T.Values);
         end if;
         F_2 := T.Struct;
      end Prove_Extract_Y;

      procedure Prove_Extract_YL with Ghost is
      begin
         if YL /= 0 then
            Prove_Extract_Order (T.Struct, F_2, Y, YL, T.Values);
            pragma Assert (Get (Model (F_2, Y) (YL).A, 1) = Left);
         else
            Prove_Preserved_Order (T.Struct, F_2, Y, T.Values);
         end if;
         Prove_Preserved_Order (T.Struct, F_2, X, T.Values);
         if not Is_Root then
            Prove_Preserved_Order (T.Struct, F_2, T.Root, T.Values);
         end if;
         F_3 := T.Struct;
      end Prove_Extract_YL;

      procedure Prove_Plug_YL with Ghost is
      begin
         if YL /= 0 then
            pragma Assert (Get (Model (T.Struct, X) (YL).A, 1) = Right);
            pragma Assert
              (for all J in Index_Type =>
                 (if Model (F_3, Y) (J).K
                  then T.Values (J) > T.Values (X)));
            pragma Assert (Ordered_Leafs (F_3, X, T.Values));
            pragma Assert (Ordered_Leafs (F_3, YL, T.Values));
            Prove_Plug_Order (T.Struct, F_3, X, YL, T.Values);
         else
            Prove_Preserved_Order (T.Struct, F_3, X, T.Values);
         end if;
         Prove_Preserved_Order (T.Struct, F_3, Y, T.Values);
         if not Is_Root then
            Prove_Preserved_Order (T.Struct, F_3, T.Root, T.Values);
         end if;
         F_4 := T.Struct;
      end Prove_Plug_YL;

      procedure Prove_Plug_X with Ghost is
      begin
         pragma Assert (Get (Model (T.Struct, Y) (X).A, 1) = Left);
         Prove_Model_Total (F_2, X, X, Right);
         pragma Assert
           (for all J in Index_Type =>
              (if Model (F_3, X) (J).K
               then T.Values (J) <= T.Values (X)));
         pragma Assert
           (for all J in Index_Type =>
              (if Model (F_4, X) (J).K
               then T.Values (J) < T.Values (Y)));
         pragma Assert (Ordered_Leafs (F_4, X, T.Values));
         pragma Assert (Ordered_Leafs (F_4, Y, T.Values));
         Prove_Plug_Order (T.Struct, F_4, Y, X, T.Values);
         if not Is_Root then
            Prove_Preserved_Order (T.Struct, F_4, T.Root, T.Values);
         end if;
         F_5 := T.Struct;
      end Prove_Plug_X;


      procedure Prove_Plug_Y with Ghost is
      begin
         pragma Assert (Model (F_5, T.Root) = Model (F_1, T.Root));
         Preserve_Equal (Model (T.Struct, T.Root) (J).A, Model (F_Old, T.Root) (J).A,
                         Model (T.Struct, T.Root) (Y).A, Model (F_Old, T.Root) (X).A, D);
         pragma Assert
           (for all I in Index_Type =>
              (if Model (F_5, Y) (I).K then Model (F_1, X) (I).K));
         pragma Assert
           (for all I in Index_Type =>
              (if Model (F_5, T.Root) (I).K
               and Model (F_5, T.Root) (I).A < Model (T.Struct, T.Root) (Y).A then
                    Model (F_1, T.Root) (I).K
               and Model (F_1, T.Root) (I).A < Model (F_Old, T.Root) (X).A));
         pragma Assert
           (for all I in Index_Type =>
              (if Model (F_5, T.Root) (I).K
               and Model (F_5, T.Root) (I).A < Model (T.Struct, T.Root) (Y).A then
               Get (Model (F_Old, T.Root) (X).A,
                 Length (Model (F_1, T.Root) (I).A) + 1)
               = Get (Model (T.Struct, T.Root) (Y).A,
                 Length (Model (F_5, T.Root) (I).A) + 1)));
         Prove_Plug_Order (T.Struct, F_5, T.Root, Y, T.Values);
      end Prove_Plug_Y;
   begin
      --  X is the subtree located at I

      if Is_Root then
         X := T.Root;
      else
         J := Parent (T.Struct, I);
         D := Position (T.Struct, I);
         Extract (T.Struct, T.Root, J, D, X);
      end if;
      Prove_Extract_X;

      --  Y is X's right subtree

      Extract (T.Struct, X, X, Right, Y);
      Prove_Extract_Y;

      --  YL is Y's left subtree

      F_2 := T.Struct;
      Extract (T.Struct, Y, Y, Left, YL);
      Prove_Extract_YL;

      --  Plug Y's left subtree into X's right subtree

      F_3 := T.Struct;
      Plug (T.Struct, X, X, Right, YL);
      Prove_Plug_YL;

      --  Plug X into Y's left subtree

      F_4 := T.Struct;
      Plug (T.Struct, Y, Y, Left, X);
      Prove_Plug_X;

      --  Y takes X's place in the tree

      if Is_Root then
         T.Root := Y;
      else
         F_5 := T.Struct;
         Plug (T.Struct, T.Root, J, D, Y);
         Prove_Plug_Y;
      end if;

      Prove_Preserved_Values (T_Old, T);
   end Left_Rotate;

   procedure Right_Rotate (T : in out Search_Tree; I : Index_Type) is
      X, Y    : Index_Type;
      XR      : Extended_Index_Type;
      Is_Root : constant Boolean := I = Root (T);
      J       : Index_Type := 1;
      D       : Direction := Left;
      T_Old   : Search_Tree := T with Ghost;
      F_Old   : Forest := T.Struct with Ghost;
      F_1, F_2, F_3, F_4, F_5 : Forest := T.Struct with Ghost;

      procedure Prove_Extract_Y with Ghost is
      begin
         if not Is_Root then
            Prove_Extract_Order (T.Struct, F_Old, T.Root, Y, T.Values);
         end if;
         F_1 := T.Struct;
      end Prove_Extract_Y;

      procedure Prove_Extract_X with Ghost is
      begin
         Prove_Extract_Order (T.Struct, F_1, Y, X, T.Values);
         pragma Assert (Get (Model (F_1, Y) (X).A, 1) = Left);
         pragma Assert (T.Values (X) < T.Values (Y));
         if not Is_Root then
            Prove_Preserved_Order (T.Struct, F_1, T.Root, T.Values);
         end if;
         F_2 := T.Struct;
      end Prove_Extract_X;

      procedure Prove_Extract_XR with Ghost is
      begin
         if XR /= 0 then
            Prove_Extract_Order (T.Struct, F_2, X, XR, T.Values);
            pragma Assert (Get (Model (F_2, X) (XR).A, 1) = Right);
         else
            Prove_Preserved_Order (T.Struct, F_2, X, T.Values);
         end if;
         Prove_Preserved_Order (T.Struct, F_2, Y, T.Values);
         if not Is_Root then
            Prove_Preserved_Order (T.Struct, F_2, T.Root, T.Values);
         end if;
         F_3 := T.Struct;
      end Prove_Extract_XR;

      procedure Prove_Plug_XR with Ghost is
      begin
         if XR /= 0 then
            pragma Assert (Get (Model (T.Struct, Y) (XR).A, 1) = Left);
            pragma Assert
              (for all J in Index_Type =>
                 (if Model (F_3, X) (J).K
                  then T.Values (J) < T.Values (Y)));
            pragma Assert (Ordered_Leafs (F_3, Y, T.Values));
            Prove_Plug_Order (T.Struct, F_3, Y, XR, T.Values);
         else
            Prove_Preserved_Order (T.Struct, F_3, Y, T.Values);
         end if;
         Prove_Preserved_Order (T.Struct, F_3, X, T.Values);
         if not Is_Root then
            Prove_Preserved_Order (T.Struct, F_3, T.Root, T.Values);
         end if;
         F_4 := T.Struct;
      end Prove_Plug_XR;

      procedure Prove_Plug_Y with Ghost is
      begin
         pragma Assert (Get (Model (T.Struct, X) (Y).A, 1) = Right);
         Prove_Model_Total (F_2, Y, Y, Left);
         pragma Assert
           (for all J in Index_Type =>
              (if XR /= 0 and then Model (F_3, XR) (J).K
               then T.Values (J) > T.Values (X)));
         pragma Assert
           (for all J in Index_Type =>
              (if Model (F_3, Y) (J).K
               then T.Values (J) >= T.Values (Y)));
         pragma Assert
           (for all J in Index_Type =>
              (if Model (F_4, Y) (J).K
               then T.Values (J) > T.Values (X)));
         pragma Assert (Ordered_Leafs (F_4, X, T.Values));
         pragma Assert (Ordered_Leafs (F_4, Y, T.Values));
         Prove_Plug_Order (T.Struct, F_4, X, Y, T.Values);
         if not Is_Root then
            Prove_Preserved_Order (T.Struct, F_4, T.Root, T.Values);
         end if;
         F_5 := T.Struct;
      end Prove_Plug_Y;


      procedure Prove_Plug_X with Ghost is
      begin
         pragma Assert (Model (F_5, T.Root) = Model (F_1, T.Root));
         Preserve_Equal (Model (T.Struct, T.Root) (J).A, Model (F_Old, T.Root) (J).A,
                         Model (T.Struct, T.Root) (X).A, Model (F_Old, T.Root) (Y).A, D);
         pragma Assert
           (for all I in Index_Type =>
              (if Model (F_5, X) (I).K then Model (F_1, Y) (I).K));
         pragma Assert
           (for all I in Index_Type =>
              (if Model (F_5, T.Root) (I).K
               and Model (F_5, T.Root) (I).A < Model (T.Struct, T.Root) (X).A then
                    Model (F_1, T.Root) (I).K
               and Model (F_1, T.Root) (I).A < Model (F_Old, T.Root) (Y).A));
         pragma Assert
           (for all I in Index_Type =>
              (if Model (F_5, T.Root) (I).K
               and Model (F_5, T.Root) (I).A < Model (T.Struct, T.Root) (X).A then
               Length (Model (F_1, T.Root) (I).A) = Length (Model (F_5, T.Root) (I).A)));
         pragma Assert
           (for all I in Index_Type =>
              (if Model (F_5, T.Root) (I).K
               and Model (F_5, T.Root) (I).A < Model (T.Struct, T.Root) (X).A then
               Get (Model (F_Old, T.Root) (Y).A,
                 Length (Model (F_5, T.Root) (I).A) + 1)
               = Get (Model (T.Struct, T.Root) (X).A,
                 Length (Model (F_5, T.Root) (I).A) + 1)));
         pragma Assert
           (for all I in Index_Type =>
              (if Model (F_5, T.Root) (I).K
               and Model (F_5, T.Root) (I).A < Model (T.Struct, T.Root) (X).A then
               Get (Model (F_Old, T.Root) (Y).A,
                 Length (Model (F_1, T.Root) (I).A) + 1)
               = Get (Model (T.Struct, T.Root) (X).A,
                 Length (Model (F_5, T.Root) (I).A) + 1)));
         pragma Assert (Ordered_Leafs (F_5, T.Root, T.Values));
         pragma Assert (Ordered_Leafs (F_4, X, T.Values));
         Prove_Plug_Order (T.Struct, F_5, T.Root, X, T.Values);
      end Prove_Plug_X;

   begin
      --  Y is the subtree located at I

      if Is_Root then
         Y := T.Root;
      else
         J := Parent (T.Struct, I);
         D := Position (T.Struct, I);
         Extract (T.Struct, T.Root, J, D, Y);
      end if;
      Prove_Extract_Y;

      --  X is Y's left subtree

      Extract (T.Struct, Y, Y, Left, X);
      Prove_Extract_X;

      --  XR is X's right subtree

      Extract (T.Struct, X, X, Right, XR);
      Prove_Extract_XR;

      --  Plug X's right subtree into Y's left subtree

      Plug (T.Struct, Y, Y, Left, XR);
      Prove_Plug_XR;

      --  Plug Y into X's right subtree

      Plug (T.Struct, X, X, Right, Y);
      Prove_Plug_Y;

      --  X takes Y's place in the tree

      if Is_Root then
         T.Root := X;
      else
         Plug (T.Struct, T.Root, J, D, X);
         Prove_Plug_X;
      end if;

      pragma Assert
        (for all J in Index_Type =>
           (if Model (T_Old) (J).K then Model (T) (J).K));
      Prove_Preserved_Values (T_Old, T);
   end Right_Rotate;

   function Mem (T : Search_Tree; V : Natural) return Boolean
   is
      Current  : Extended_Index_Type := T.Root;
      Previous : Extended_Index_Type := T.Root with Ghost;
      D        : Direction := Left with Ghost;
   begin
      while Current /= 0 loop
         pragma Loop_Invariant (Model (T.Struct, T.Root) (Current).K);
         pragma Loop_Invariant
           (for all I in Index_Type =>
              (if Model (T.Struct, T.Root) (I).K then
                   (if Model (T.Struct, T.Root) (I).A < Model (T.Struct, T.Root) (Current).A
                    then (if Get (Model (T.Struct, T.Root) (Current).A, Length (Model (T.Struct, T.Root) (I).A) + 1) = Left then
                         V < T.Values (I)
                      else V > T.Values (I)))));
         Previous := Current;
         if V = T.Values (Current) then
            return True;
         elsif V < T.Values (Current) then
            D := Left;
            Current := Peek (T.Struct, Current, Left);
         else
            D := Right;
            Current := Peek (T.Struct, Current, Right);
         end if;
      end loop;
      if Size (T.Struct) > 0 then
         Prove_Order_Total (T, Previous, V);
      end if;
      return False;
   end Mem;

   procedure Insert
     (T : in out Search_Tree; V : Natural; I : out Extended_Index_Type)
   is
      T_Old : Search_Tree := T;

      procedure Prove_Ordered_Leafs (T : Search_Tree; L : Index_Type; D : Direction) with Ghost,
        Pre  => Size (T_Old.Struct) > 0 and then T_Old.Values (L) /= V
        and then Model (T_Old.Struct, T_Old.Root) (L).K
        and then
          (if V < T_Old.Values (L) then D = Left else D = Right)
        and then Peek (T_Old.Struct, L, D) = 0
        and then
          (for all I in Index_Type =>
             (if Model (T_Old.Struct, T_Old.Root) (I).K then
                  (if Model (T_Old.Struct, T_Old.Root) (I).A < Model (T_Old.Struct, T_Old.Root) (L).A
                         then (if Get (Model (T_Old.Struct, T_Old.Root) (L).A, Length (Model (T_Old.Struct, T_Old.Root) (I).A) + 1) = Left then
                                 V < T_Old.Values (I)
                               else V > T_Old.Values (I)))))
        and then Size (T.Struct) = Size (T_Old.Struct) + 1
        and then T.Root = T_Old.Root
        and then Valid_Root (T.Struct, T.Root)
        and then I /= 0 and then Peek (T.Struct, L, D) = I
        and then
          (for all J in Index_Type =>
             (if Model (T.Struct, T.Root) (J).K then
                  Model (T_Old.Struct, T.Root) (J).K or J = I))
        and then
          (for all J in Index_Type =>
             (if Model (T_Old.Struct, T.Root) (J).K then Model (T.Struct, T.Root) (J).K))
        and then
          (for all J in Index_Type =>
             (if Model (T_Old.Struct, T.Root) (J).K
                  then Model (T.Struct, T.Root) (J).A = Model (T_Old.Struct, T.Root) (J).A))
        and then
          Is_Add (Model (T.Struct, T.Root) (L).A, D, Model (T.Struct, T.Root) (I).A)
        and then
          (for all J in Index_Type =>
             (if Model (T_Old.Struct, T.Root) (J).K then T.Values (J) = T_Old.Values (J)))
        and then T.Values (I) = V,
        Post => Ordered_Leafs (T.Struct, T.Root, T.Values)
      is
      begin
         for KI in Index_Type loop
            if KI = I then
               Prove_Model_Total (T_Old.Struct, T.Root, L, D);
               pragma Assert
                 (for all J in Index_Type =>
                    (if Model (T_Old.Struct, T.Root) (J).K
                     and then Model (T.Struct, T.Root) (L).A < Model (T.Struct, T.Root) (J).A
                     then Get (Model (T.Struct, T.Root) (J).A, Length (Model (T.Struct, T.Root) (L).A) + 1) /= D));
               pragma Assert
                 (for all J in Index_Type =>
                         (if Model (T.Struct, T.Root) (J).K then
                          not (Model (T.Struct, T.Root) (I).A < Model (T.Struct, T.Root) (J).A)));
            else
               pragma Assert
                 (for all J in Index_Type =>
                    (if Model (T.Struct, T.Root) (KI).K
                     and then Model (T.Struct, T.Root) (J).K and then J /= I
                     and then Model (T.Struct, T.Root) (KI).A < Model (T.Struct, T.Root) (J).A
                     then (if Get (Model (T.Struct, T.Root) (J).A, Length (Model (T.Struct, T.Root) (KI).A) + 1) = Left then
                            T.Values (J) < T.Values (KI)
                       else T.Values (J) > T.Values (KI))));
               pragma Assert
                 (if Model (T.Struct, T.Root) (KI).K then
                      (if Model (T.Struct, T.Root) (KI).A < Model (T.Struct, T.Root) (I).A
                       then KI = L or Model (T.Struct, T.Root) (KI).A < Model (T.Struct, T.Root) (L).A));
               pragma Assert
                 (for all J in Index_Type =>
                    (if Model (T.Struct, T.Root) (KI).K and then KI /= L
                     and then Model (T.Struct, T.Root) (J).K
                     and then Model (T.Struct, T.Root) (KI).A < Model (T.Struct, T.Root) (J).A
                     then (if Get (Model (T.Struct, T.Root) (J).A, Length (Model (T.Struct, T.Root) (KI).A) + 1) = Left then
                            T.Values (J) < T.Values (KI)
                           else T.Values (J) > T.Values (KI))));
            end if;
            pragma Loop_Invariant
              (for all I in 1 .. KI =>
                 (for all J in Index_Type =>
                      (if Model (T.Struct, T.Root) (I).K
                       and then Model (T.Struct, T.Root) (J).K
                       and then Model (T.Struct, T.Root) (I).A < Model (T.Struct, T.Root) (J).A
                       then (if Get (Model (T.Struct, T.Root) (J).A, Length (Model (T.Struct, T.Root) (I).A) + 1) = Left then
                                T.Values (J) < T.Values (I)
                             else T.Values (J) > T.Values (I)))));
         end loop;

         pragma Assert
           (for all I in Index_Type =>
              (for all J in Index_Type =>
                   (if Model (T.Struct, T.Root) (I).K then
                      (if Model (T.Struct, T.Root) (J).K
                       and then Model (T.Struct, T.Root) (I).A < Model (T.Struct, T.Root) (J).A
                       then (if Get (Model (T.Struct, T.Root) (J).A, Length (Model (T.Struct, T.Root) (I).A) + 1) = Left then
                              T.Values (J) < T.Values (I)
                             else T.Values (J) > T.Values (I))))));
      end Prove_Ordered_Leafs;

   begin
      if T.Root = 0 then
         Init (T.Struct, I);
         T.Values (I) := V;
         T.Root := I;
         return;
      end if;

      declare
         Current  : Extended_Index_Type := T.Root;
         Previous : Extended_Index_Type := 0;
         D        : Direction := Left;
      begin
         while Current /= 0 loop
            pragma Loop_Invariant (Model (T.Struct, T.Root) (Current).K);
            pragma Loop_Invariant
              (for all I in Index_Type =>
                 (if Model (T.Struct, T.Root) (I).K then
                      (if Model (T.Struct, T.Root) (I).A < Model (T.Struct, T.Root) (Current).A
                       then (if Get (Model (T.Struct, T.Root) (Current).A, Length (Model (T.Struct, T.Root) (I).A) + 1) = Left then
                            V < T.Values (I)
                       else V > T.Values (I)))));
            Previous := Current;
            if V = T.Values (Previous) then
               I := 0;
               pragma Assert (for some I in Index_Type =>
                                Model (T) (I).K and then T.Values (I) = V);
               pragma Assert (Mem (T, V));
               return;
            elsif V < T.Values (Previous) then
               D := Left;
            else
               D := Right;
            end if;
            Current := Peek (T.Struct, Previous, D);
         end loop;

         Prove_Order_Total (T, Previous, V);

         Insert (T.Struct, T.Root, Previous, D, I);
         T.Values (I) := V;
         Prove_Ordered_Leafs (T, Previous, D);
      end;
   end Insert;

end Search_Trees;
