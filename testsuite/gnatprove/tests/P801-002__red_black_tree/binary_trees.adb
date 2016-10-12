package body Binary_Trees with SPARK_Mode is

   function Tree_Structure (F : Forest) return Boolean is

      --  Cells that are not allocated yet have default values

     ((for all I in F.S + 1 .. Max => F.C (I) = (0, 0, 0, Top))

      --  Parent and children of allocated cells are allocated

      and then
        (for all I in Index_Type => F.C (I).Parent in 0 .. F.S)
      and then
        (for all I in Index_Type => F.C (I).Left in 0 .. F.S)
      and then
        (for all I in Index_Type => F.C (I).Right in 0 .. F.S)

      --  If a cell is the root of a tree (position Top) it has no parent

      and then
        (for all I in Index_Type =>
             (if F.C (I).Position = Top then F.C (I).Parent = 0))

      --  If a cell I has a left child, then its left child has position Left
      --  and parent I.

      and then
        (for all I in Index_Type =>
             (if F.C (I).Left /= 0 then F.C (F.C (I).Left).Position = Left
              and then F.C (F.C (I).Left).Parent = I))

      --  If a cell I has a right child, then its right child has position Right
      --  and parent I.

      and then
        (for all I in Index_Type =>
             (if F.C (I).Right /= 0 then F.C (F.C (I).Right).Position = Right
              and then F.C (F.C (I).Right).Parent = I))

      --  If a cell is a child (position Left or Right), then it is the child
      --  of its parent

      and then
        (for all I in Index_Type =>
             (if F.C (I).Parent /= 0 and then F.C (I).Position = Left
              then F.C (F.C (I).Parent).Left = I))
      and then
        (for all I in Index_Type =>
             (if F.C (I).Parent /= 0 and then F.C (I).Position = Right
              then F.C (F.C (I).Parent).Right = I)));

   function Valid_Root (F : Forest; I : Index_Type) return Boolean is
     (I <= F.S and then F.C (I).Position = Top);

   function Size (F : Forest) return Extended_Index_Type is (F.S);

   function Parent (F : Forest; I : Index_Type) return Extended_Index_Type is
     (F.C (I).Parent);

   function Position (F : Forest; I : Index_Type) return Direction is
     (F.C (I).Position);

   function Model (F : Forest; Root : Index_Type) return Model_Type is
      type Boolean_Array is array (Index_Type) of Boolean;

      function Next (ToDo : Boolean_Array) return Extended_Index_Type with
        Post =>
          (if Next'Result = 0 then (for all I in ToDo'Range => not ToDo (I))
           else ToDo (Next'Result))
      is
      begin
         for I in ToDo'Range loop
            pragma Loop_Invariant (for all J in 1 .. I - 1 => not ToDo (J));
            if ToDo (I) then
               return I;
            end if;
         end loop;
         return 0;
      end Next;

      ToDo : Boolean_Array := (others => False);
      --  The array containing the nodes that are still to analyze

      R    : Model_Type;
      I    : Extended_Index_Type := Root;
      N    : Extended_Index_Type := 0 with Ghost;

   begin
      --  Insert the root in R and store it in the ToDo list

      ToDo (Root) := True;
      R (Root).K := True;

      --  Loop until the ToDO list is empty. Note that we do not prove the
      --  termination of the loop but assume it

      while I /= 0 loop
         pragma Loop_Invariant (ToDo (I));
         pragma Loop_Invariant
           (for all J in Index_Type =>
              (if ToDo (J) then R (J).K));
         pragma Loop_Invariant
           (for all J in Index_Type =>
              (if ToDo (J) then
                   (for all K in Index_Type =>
                        (if R (K).K then not (R (J).A < R (K).A)))));
         pragma Loop_Invariant (R (Root).K and Length (R (Root).A) = 0);
         pragma Loop_Invariant
           (for all J in Index_Type =>
              (if R (J).K and J /= Root then F.C (J).Parent /= 0
               and then R (F.C (J).Parent).K));
         pragma Loop_Invariant
           (for all J in Index_Type =>
                (if R (J).K and J /= Root then
                      Is_Add (R (F.C (J).Parent).A, F.C (J).Position, R (J).A)
                 else Length (R (J).A) = 0));
         pragma Loop_Invariant
           (for all J in Index_Type =>
              (if J /= Root then
                   (if F.C (J).Parent /= 0 and then R (F.C (J).Parent).K then
                       R (J).K or ToDo (F.C (J).Parent)
                    else not R (J).K)));
         pragma Loop_Invariant
           (for all J in Index_Type =>
              (if R (J).K and then J /= Root then not ToDo (F.C (J).Parent)));
         pragma Loop_Invariant
           (for all J in Index_Type =>
              (if R (J).K then
                   (for all K in Index_Type =>
                        (if R (K).K and R (K).A = R (J).A
                         then J = K))));
         pragma Loop_Invariant (R (Root).K and Length (R (Root).A) = 0);
         pragma Loop_Invariant (for all J in Index_Type => Length (R (J).A) <= N);
         pragma Loop_Invariant (N < Max);
         pragma Loop_Variant (Increases => N);

         declare
            J : Extended_Index_Type;
         begin
            J := F.C (I).Left;
            if J /= 0 then
               R (J).K := True;
               R (J).A := Add (R (F.C (J).Parent).A, Left);
               ToDo (J) := True;
            end if;
            J := F.C (I).Right;
            if J /= 0 then
               R (J).K := True;
               R (J).A := Add (R (F.C (J).Parent).A, Right);
               ToDo (J) := True;
            end if;
         end;
         ToDo (I) := False;
         I := Next (ToDo);
         N := N + 1;
         pragma Assume (if I /= 0 then N < Max);
      end loop;
      pragma Assert
        (for all J in Index_Type =>
           (if J /= Root then
                (if F.C (J).Parent /= 0 and then R (F.C (J).Parent).K then
                    R (J).K or ToDo (F.C (J).Parent)
                 else not R (J).K)));
      return R;
   end Model;

   procedure Preserve_Equal (S1, S2, S3, S4 : Sequence; D : Direction) with
     Ghost,
     Pre  => S1 = S2 and Is_Add (S1, D, S3) and Is_Add (S2, D, S4),
     Post => S3 = S4 is
   begin
      null;
   end Preserve_Equal;

   procedure Preserve_Concat (S1, S2, S3, S4, T : Sequence; D : Direction) with
     Ghost,
     Pre  => Is_Concat (T, S1, S2) and Is_Add (S1, D, S3) and Is_Add (S2, D, S4),
     Post => Is_Concat (T, S3, S4) is
   begin
      null;
   end Preserve_Concat;

   procedure Prove_Model_Distinct (F : Forest; T1, T2 : Index_Type)
   is
   begin
      for N in Index_Type loop
         pragma Loop_Invariant
           (for all I in Index_Type =>
              (if Model (F, T1) (I).K and Length (Model (F, T1) (I).A) < N then
                    not Model (F, T2) (I).K));
      end loop;
   end Prove_Model_Distinct;

   procedure Prove_Model_Preserved (F1, F2 : Forest; Root : Index_Type) with Ghost,
     Pre  => Tree_Structure (F1) and then Tree_Structure (F2)
     and then F1.C (Root).Position = Top
     and then Root in 1 .. F1.S and then F2.S >= F1.S
     and then (for all I in Index_Type =>
                 (if Model (F1, Root) (I).K then F1.C (I) = F2.C (I))),
     Post => F2.C (Root).Position = Top
     and then Model (F1, Root) = Model (F2, Root)
   is
   begin
      for N in Index_Type loop
         pragma Loop_Invariant
           (for all I in Index_Type =>
              (if Model (F1, Root) (I).K and Length (Model (F1, Root) (I).A) < N then
                    Model (F2, Root) (I).K));
         pragma Loop_Invariant
           (for all I in Index_Type =>
              (if Model (F1, Root) (I).K and Length (Model (F1, Root) (I).A) < N then
                  Model (F2, Root) (I).A = Model (F1, Root) (I).A));
         pragma Loop_Invariant
           (for all I in Index_Type =>
              (if Model (F2, Root) (I).K and Length (Model (F2, Root) (I).A) < N then
                    Model (F1, Root) (I).K));
         for J in Index_Type loop
            if Model (F1, Root) (J).K and Length (Model (F1, Root) (J).A) = N then
               Preserve_Equal (Model (F1, Root) (F1.C (J).Parent).A, Model (F2, Root) (F1.C (J).Parent).A,
                               Model (F1, Root) (J).A, Model (F2, Root) (J).A, F1.C (J).Position);
            end if;
            pragma Loop_Invariant
              (for all I in 1 .. J =>
                 (if Model (F1, Root) (I).K and Length (Model (F1, Root) (I).A) = N then
                       Model (F2, Root) (I).A = Model (F1, Root) (I).A));
         end loop;
      end loop;
   end Prove_Model_Preserved;

   procedure Prove_Model_Total (F : Forest; Root : Index_Type) is
   begin
      for N in Index_Type loop
         pragma Loop_Invariant
           (for all I in Index_Type =>
              (if Model (F, Root) (I).K then
                   (for all D in Direction =>
                        (if Peek (F, I, D) = 0 then
                           (for all J in Index_Type =>
                              (if Model (F, Root) (J).K
                               and then Model (F, Root) (I).A < Model (F, Root) (J).A
                               and then Length (Model (F, Root) (J).A) <= Length (Model (F, Root) (I).A) + N
                               then Get (Model (F, Root) (J).A, Length (Model (F, Root) (I).A) + 1) /= D))))));
      end loop;
   end Prove_Model_Total;

   procedure Prove_Peek_Preserved (F1, F2 : Forest; Root, I : Index_Type; D : Direction) is
   begin
      raise Program_Error;
   end Prove_Peek_Preserved;

   function Peek (F : Forest; I : Index_Type; D : Direction) return Extended_Index_Type is
      (if D = Left then F.C (I).Left else F.C (I).Right);

   procedure Extract (F : in out Forest; Root, I : Index_Type; D : Direction; V : out Extended_Index_Type) is
      F_Old : Forest := F with Ghost;

      procedure Prove_Post with Ghost,
        Pre  =>  F.S = F_Old.S and then Root <= F.S and then V in 1 .. F.S
        and then F_Old.C (Root).Position = Top and then V /= Root
        and then F.C (V).Position = Top and then Model (F_Old, Root) (V).K
        and then (for all I in Index_Type =>
                    (if I /= V then F.C (I).Parent = F_Old.C (I).Parent))
        and then (for all I in Index_Type =>
                    (if I /= V then  F.C (I).Position = F_Old.C (I).Position))
        and then (for all J in Index_Type =>
                    (if not Model (F_Old, Root) (J).K then
                         F.C (J).Left = F_Old.C (J).Left))
        and then (for all J in Index_Type =>
                    (if not Model (F_Old, Root) (J).K then
                         F.C (J).Right = F_Old.C (J).Right)),
        Post =>
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
               (if Model (F, V) (I).K then Model (F_Old, Root) (I).K))
          and then
            (for all I in Index_Type =>
               (if Model (F, Root) (I).K then Model (F, Root) (I).A = Model (F_Old, Root) (I).A))
          and then
            (for all I in Index_Type =>
               (if Model (F, V) (I).K then
                    Is_Concat (Model (F_Old, Root) (V).A, Model (F, V) (I).A, Model (F_Old, Root) (I).A)))
          and then
            (for all R in 1 .. F.S =>
               (if R /= Root and R /= V and F_Old.C (R).Position = Top then
                Model (F_Old, R) = Model (F, R)))
      is
      begin
         pragma Assert (F.C (Root).Position = Top);
         pragma Assert
           (for all I in Index_Type =>
              (if F.C (I).Parent > 0 and then Model (F, V) (F.C (I).Parent).K
               then I /= V and then Model (F, V) (I).K));
         pragma Assert (not (Model (F, Root) (V).K));
         for N in Index_Type loop
            pragma Loop_Invariant
              (for all I in Index_Type =>
                 (if Model (F_Old, Root) (I).K and then Length (Model (F_Old, Root) (I).A) <= N - 1 then
                      (if Model (F_Old, Root) (V).A <= Model (F_Old, Root) (I).A then
                              Model (F, V) (I).K
                       else Model (F, Root) (I).K)));
            pragma Loop_Invariant
              (for all I in Index_Type =>
                 (if Model (F, Root) (I).K and then Length (Model (F, Root) (I).A) <= N - 1
                  then Model (F_Old, Root) (I).K));
            pragma Loop_Invariant
              (for all I in Index_Type =>
                 (if Model (F, V) (I).K and then Length (Model (F, V) (I).A) <= N - 1
                  then Model (F_Old, Root) (I).K));
            pragma Loop_Invariant
              (for all I in Index_Type =>
                 (if Model (F_Old, Root) (I).K and then Length (Model (F_Old, Root) (I).A) <= N - 1 then
                      (if Model (F, Root) (I).K then Model (F, Root) (I).A = Model (F_Old, Root) (I).A)));
            pragma Loop_Invariant
              (for all I in Index_Type =>
                 (if Model (F_Old, Root) (I).K and then Length (Model (F_Old, Root) (I).A) <= N - 1 then
                      (if Model (F, V) (I).K then
                              Is_Concat (Model (F_Old, Root) (V).A, Model (F, V) (I).A, Model (F_Old, Root) (I).A))));

            for KI in Index_Type loop
               if Model (F_Old, Root) (KI).K and then Length (Model (F_Old, Root) (KI).A) = N and then Model (F, Root) (KI).K then
                  Preserve_Equal (Model (F, Root) (F.C (KI).Parent).A, Model (F_Old, Root) (F.C (KI).Parent).A, Model (F, Root) (KI).A, Model (F_Old, Root) (KI).A, F.C (KI).Position);
               end if;
               if Model (F_Old, Root) (KI).K and then Length (Model (F_Old, Root) (KI).A) = N and then Model (F, V) (KI).K and then KI /= V then
                  Preserve_Concat (Model (F, V) (F.C (KI).Parent).A, Model (F_Old, Root) (F.C (KI).Parent).A, Model (F, V) (KI).A, Model (F_Old, Root) (KI).A, Model (F_Old, Root) (V).A, F.C (KI).Position);
               end if;
               pragma Loop_Invariant
                 (for all I in 1 .. KI =>
                    (if Model (F_Old, Root) (I).K and then Length (Model (F_Old, Root) (I).A) <= N then
                         (if Model (F, Root) (I).K then Model (F, Root) (I).A = Model (F_Old, Root) (I).A)));
               pragma Loop_Invariant
                 (for all I in 1 .. KI =>
                    (if Model (F_Old, Root) (I).K and then Length (Model (F_Old, Root) (I).A) <= N then
                         (if Model (F, V) (I).K then
                                 Is_Concat (Model (F_Old, Root) (V).A, Model (F, V) (I).A, Model (F_Old, Root) (I).A))));
            end loop;
         end loop;

         for R in 1 .. F_Old.S loop
            if R /= Root and R /= V and F_Old.C (R).Position = Top then
               Prove_Model_Distinct (F_Old, Root, R);
               Prove_Model_Preserved (F_Old, F, R);
            end if;
            pragma Loop_Invariant
              (for all P in 1 .. R =>
                 (if P /= Root and P /= V and F_Old.C (P).Position = Top then
                       Model (F_Old, P) = Model (F, P)));
         end loop;
      end Prove_Post;
   begin
      V := (if D = Left then F.C (I).Left else F.C (I).Right);

      if V /= 0 then
         if D = Left then
            F.C (I).Left := 0;
         else
            F.C (I).Right := 0;
         end if;
         pragma Assert (F.C (V).Parent = I);
         F.C (V).Position := Top;
         F.C (V).Parent := 0;
      end if;

      pragma Assert
        (for all I in Index_Type =>
             (if F.C (I).Parent /= 0 and then F.C (I).Position = Left
              then F.C (F.C (I).Parent).Left = I));
      pragma Assert
        (for all I in Index_Type =>
             (if F.C (I).Parent /= 0 and then F.C (I).Position = Right
              then F.C (F.C (I).Parent).Right = I));

      if V /= 0 then
         Prove_Post;
      end if;
   end Extract;

   procedure Plug (F : in out Forest; Root, I : Index_Type; D : Direction; V : Extended_Index_Type) is
      F_Old : Forest := F with Ghost;

      procedure Prove_Post with Ghost,
        Pre  =>  F.S = F_Old.S and then Root <= F.S and then V in 1 .. F.S
        and then F.C (Root).Position = Top and then V /= Root
        and then F_Old.C (Root).Position = Top
        and then F_Old.C (V).Position = Top
        and then F.C (V).Parent > 0
        and then Model (F_Old, Root) (F.C (V).Parent).K
        and then (for all I in Index_Type =>
                    (if I /= V then F.C (I).Parent = F_Old.C (I).Parent))
        and then (for all I in Index_Type =>
                    (if I /= V then  F.C (I).Position = F_Old.C (I).Position))
        and then (for all J in Index_Type =>
                    (if not Model (F_Old, Root) (J).K then
                         F.C (J).Left = F_Old.C (J).Left))
        and then (for all J in Index_Type =>
                    (if not Model (F_Old, Root) (J).K then
                         F.C (J).Right = F_Old.C (J).Right)),
        Post =>   Model (F, Root) (V).K
          and then
          (for all I in Index_Type =>
             (if Model (F, Root) (I).K then
                  Model (F_Old, V) (I).K or Model (F_Old, Root) (I).K))
          and then
            (for all I in Index_Type =>
               (if Model (F_Old, Root) (I).K then Model (F, Root) (I).K))
          and then
            (for all I in Index_Type =>
               (if Model (F_Old, V) (I).K then Model (F, Root) (I).K))
          and then
            (for all I in Index_Type =>
               (if Model (F_Old, Root) (I).K then Model (F, Root) (I).A = Model (F_Old, Root) (I).A))
          and then
            (for all I in Index_Type =>
               (if Model (F_Old, V) (I).K then
                    Is_Concat (Model (F, Root) (V).A, Model (F_Old, V) (I).A, Model (F, Root) (I).A)))
          and then
            (for all R in 1 .. F.S =>
               (if R /= Root and R /= V and F_Old.C (R).Position = Top then
                Model (F_Old, R) = Model (F, R)))
      is
      begin
         for N in Index_Type loop
            pragma Loop_Invariant
              (for all I in Index_Type =>
                 (if Model (F, Root) (I).K and then Length (Model (F, Root) (I).A) <= N - 1 then
                      Model (F_Old, V) (I).K or Model (F_Old, Root) (I).K));
            pragma Loop_Invariant
              (for all I in Index_Type =>
                 (if Model (F_Old, Root) (I).K and then Length (Model (F_Old, Root) (I).A) <= N - 1
                  then Model (F, Root) (I).K));
            pragma Loop_Invariant
              (for all I in Index_Type =>
                 (if Model (F_Old, V) (I).K and then Length (Model (F_Old, V) (I).A) <= N - 1
                  and then Model (F, Root) (F.C (V).Parent).K
                  then Model (F, Root) (I).K));
            pragma Loop_Invariant
              (for all I in Index_Type =>
                 (if Model (F, Root) (I).K and then Length (Model (F, Root) (I).A) <= N - 1 then
                      (if Model (F_Old, Root) (I).K then Model (F, Root) (I).A = Model (F_Old, Root) (I).A)));
            pragma Loop_Invariant
              (for all I in Index_Type =>
                 (if Model (F, Root) (I).K and then Length (Model (F, Root) (I).A) <= N - 1 then
                      (if Model (F_Old, V) (I).K then
                              Is_Concat (Model (F, Root) (V).A, Model (F_Old, V) (I).A, Model (F, Root) (I).A))));

            for KI in Index_Type loop
               if Model (F, Root) (KI).K and then Length (Model (F, Root) (KI).A) = N and then Model (F_Old, Root) (KI).K then
                  Preserve_Equal (Model (F, Root) (F.C (KI).Parent).A, Model (F_Old, Root) (F.C (KI).Parent).A, Model (F, Root) (KI).A, Model (F_Old, Root) (KI).A, F.C (KI).Position);
               end if;
               if Model (F, Root) (KI).K and then Length (Model (F, Root) (KI).A) = N and then Model (F_Old, V) (KI).K and then KI /= V then
                  Preserve_Concat (Model (F_Old, V) (F.C (KI).Parent).A, Model (F, Root) (F.C (KI).Parent).A, Model (F_Old, V) (KI).A, Model (F, Root) (KI).A, Model (F, Root) (V).A, F.C (KI).Position);
               end if;
               pragma Loop_Invariant
                 (for all I in 1 .. KI =>
                    (if Model (F, Root) (I).K and then Length (Model (F, Root) (I).A) <= N then
                         (if Model (F_Old, Root) (I).K then Model (F, Root) (I).A = Model (F_Old, Root) (I).A)));
               pragma Loop_Invariant
                 (for all I in 1 .. KI =>
                    (if Model (F, Root) (I).K and then Length (Model (F, Root) (I).A) <= N then
                         (if Model (F_Old, V) (I).K then
                                 Is_Concat (Model (F, Root) (V).A, Model (F_Old, V) (I).A, Model (F, Root) (I).A))));
            end loop;
         end loop;
         pragma Assert
           (for all I in Index_Type =>
              (if Model (F_Old, V) (I).K then Model (F, Root) (I).K));

         for R in 1 .. F_Old.S loop
            if R /= Root and R /= V and F_Old.C (R).Position = Top then
               Prove_Model_Distinct (F_Old, Root, R);
               Prove_Model_Distinct (F_Old, V, R);
               Prove_Model_Preserved (F_Old, F, R);
            end if;
            pragma Loop_Invariant
              (for all P in 1 .. R =>
                 (if P /= Root and P /= V and F_Old.C (P).Position = Top then
                       Model (F, P) = Model (F_Old, P)));
         end loop;
      end Prove_Post;
   begin
      if V /= 0 then
         if D = Left then
            F.C (I).Left := V;
         else
            F.C (I).Right := V;
         end if;
         F.C (V).Position := D;
         F.C (V).Parent := I;

         Prove_Post;
      end if;
   end Plug;

   procedure Insert (F : in out Forest; Root, I : Index_Type; D : Direction; V : out Index_Type) is
      F_Old : Forest := F with Ghost;

      procedure Prove_Post with Ghost,
        Pre  => F_Old.C (Root).Position = Top and then V /= 0
        and then Root in 1 .. F_Old.S
        and then F.S >= F_Old.S
        and then not Model (F_Old, Root) (V).K
        and then F.C (V).Parent > 0
        and then Model (F_Old, Root) (F.C (V).Parent).K
        and then F.C (V).Left = 0
        and then F.C (V).Right = 0
        and then (for all I in Index_Type =>
                    (if I /= V
                     then F.C (I).Parent = F_Old.C (I).Parent))
        and then (for all I in Index_Type =>
                    (if I /= V
                     then F.C (I).Position = F_Old.C (I).Position))
        and then (for all V in Index_Type =>
                    (if not Model (F_Old, Root) (V).K then
                         F.C (V).Left = F_Old.C (V).Left))
        and then (for all V in Index_Type =>
                    (if not Model (F_Old, Root) (V).K then
                         F.C (V).Right = F_Old.C (V).Right)),
        Post =>
          (for all I in Index_Type =>
             (if Model (F_Old, Root) (I).K then Model (F, Root) (I).K))
        and then
          Model (F, Root) (V).K
        and then
          (for all I in Index_Type =>
             (if Model (F, Root) (I).K and I /= V then Model (F_Old, Root) (I).K))
        and then
          (for all I in Index_Type =>
             (if Model (F_Old, Root) (I).K then Model (F, Root) (I).A = Model (F_Old, Root) (I).A))
        and then
          (for all R in 1 .. F_Old.S =>
             (if R /= Root and F_Old.C (R).Position = Top and R /= V then
                  Model (F_Old, R) = Model (F, R)))
      is
      begin
         for N in Index_Type loop
            pragma Loop_Invariant
              (for all I in Index_Type =>
                 (if Model (F_Old, Root) (I).K and then Length (Model (F_Old, Root) (I).A) < N
                  then Model (F, Root) (I).K));
            pragma Loop_Invariant
              (for all I in Index_Type =>
                 (if Model (F_Old, Root) (I).K and then Length (Model (F_Old, Root) (I).A) < N
                  then Model (F, Root) (I).A = Model (F_Old, Root) (I).A));
            pragma Loop_Invariant
              (for all I in Index_Type =>
                 (if Model (F, Root) (I).K and then Length (Model (F, Root) (I).A) < N
                  and then I /= V
                  then Model (F_Old, Root) (I).K));
            for KI in Index_Type loop
               if Model (F_Old, Root) (KI).K and then Length (Model (F_Old, Root) (KI).A) = N then
                  Preserve_Equal (Model (F, Root) (F.C (KI).Parent).A, Model (F_Old, Root) (F.C (KI).Parent).A, Model (F, Root) (KI).A, Model (F_Old, Root) (KI).A, F.C (KI).Position);
               end if;
               pragma Loop_Invariant
                 (for all I in 1 .. KI =>
                    (if Model (F_Old, Root) (I).K and then Length (Model (F_Old, Root) (I).A) <= N then
                         Model (F, Root) (I).A = Model (F_Old, Root) (I).A));
            end loop;
         end loop;
         for R in 1 .. F_Old.S loop
            if R /= Root and F_Old.C (R).Position = Top and R /= V then
               Prove_Model_Distinct (F_Old, Root, R);
               Prove_Model_Preserved (F_Old, F, R);
            end if;
            pragma Loop_Invariant
              (for all P in 1 .. R =>
                 (if P /= Root and F_Old.C (P).Position = Top and P /= V then
                       Model (F_Old, P) = Model (F, P)));
         end loop;
      end Prove_Post;

   begin
      V := F.S + 1;

      --  Plug it as the D son of I

      F.C (V).Position := D;
      F.C (V).Parent := I;

      if D = Left then
         F.C (I).Left := V;
      else
         F.C (I).Right := V;
      end if;

      F.S := F.S + 1;

      pragma Assert
        (for all I in Index_Type =>
             (if F.C (I).Parent /= 0 and then F.C (I).Position = Left
              then F.C (F.C (I).Parent).Left = I));
      pragma Assert
        (for all I in Index_Type =>
             (if F.C (I).Parent /= 0 and then F.C (I).Position = Right
              then F.C (F.C (I).Parent).Right = I));
      Prove_Post;
   end Insert;

   procedure Init (F : in out Forest; Root : out Index_Type) is
      F_Old : Forest := F with Ghost;

      procedure Prove_Post with Ghost,
        Pre  => Root in F_Old.S + 1 .. F.S
        and then (for all I in Index_Type =>
                    F.C (I).Parent = F_Old.C (I).Parent)
        and then (for all I in Index_Type =>
                    F.C (I).Position = F_Old.C (I).Position)
        and then (for all J in Index_Type =>
                    F.C (J).Left = F_Old.C (J).Left)
        and then (for all J in Index_Type =>
                    F.C (J).Right = F_Old.C (J).Right),
        Post =>
          (for all R in 1 .. F_Old.S =>
             (if F_Old.C (R).Position = Top then
                  Model (F_Old, R) = Model (F, R)))
          and then
          (for all I in Index_Type =>
            (if I /= Root then not Model (F, Root) (I).K))
      is
      begin
         for N in Extended_Index_Type loop
            pragma Loop_Invariant
              (for all J in Index_Type =>
                 (if Model (F, Root) (J).K and then J /= Root
                  then Length (Model (F, Root) (J).A) > N));
         end loop;
         for R in 1 .. F_Old.S loop
            if F_Old.C (R).Position = Top then
               Prove_Model_Preserved (F_Old, F, R);
            end if;
            pragma Loop_Invariant
              (for all P in 1 .. R =>
                 (if F_Old.C (P).Position = Top then
                       Model (F_Old, P) = Model (F, P)));
         end loop;
      end Prove_Post;
   begin
      F.S := F.S + 1;
      Root := F.S;
      Prove_Post;
   end Init;

end Binary_Trees;
