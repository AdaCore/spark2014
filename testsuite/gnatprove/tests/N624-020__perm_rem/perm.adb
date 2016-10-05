package body Perm with SPARK_Mode is

   function Remove (A : Nat_Array; I : Index) return Nat_Array is
      subtype Result_Ty is Nat_Array (1 .. A'Last - 1);
      Result : Result_Ty :=
        A (1 .. I - 1) & A (I + 1 .. A'Last);
   begin
      return Result;
   end Remove;

   function Get_Witness (A, B : Nat_Array; Ia : Index) return Index with
     Pre  => Invariant (A) and then Invariant (B) and then Ia in A'Range and then
     (for some Ib in B'Range => A (Ia) = B (Ib) and then
          Is_Perm (Remove (A, Ia), Remove (B, Ib))),
     Post => Get_Witness'Result in B'Range and then
     A (Ia) = B (Get_Witness'Result) and then
     Is_Perm (Remove (A, Ia),
              Remove (B, Get_Witness'Result));

   function Get_Witness (A, B : Nat_Array; Ia : Index) return Index is
   begin
      for Ib in B'Range loop
         if A (Ia) = B (Ib) and then
           Is_Perm (Remove (A, Ia), Remove (B, Ib))
         then
            return Ib;
         end if;
         pragma Loop_Invariant
           (for all Kb in 1 .. Ib =>
               not (A (Ia) = B (Kb) and then
              Is_Perm (Remove (A, Ia), Remove (B, Kb))));
      end loop;
      pragma Assert (False);
      return B'Last;
   end Get_Witness;

   type Witnesses is record
      Ia, Ib : Index;
   end record;

   function Get_Witnesses (A, B : Nat_Array) return Witnesses with
     Pre  => Invariant (A) and then Invariant (B) and then
     Is_Perm (A, B) and then A'Length > 0,
     Post => Get_Witnesses'Result.Ia in A'Range and then
     Get_Witnesses'Result.Ib in B'Range and then
     A (Get_Witnesses'Result.Ia) = B (Get_Witnesses'Result.Ib) and then
     Is_Perm (Remove (A, Get_Witnesses'Result.Ia),
              Remove (B, Get_Witnesses'Result.Ib));

   function Get_Witnesses (A, B : Nat_Array) return Witnesses is
   begin
      for Ia in A'Range loop
         if (for some Ib in B'Range => A (Ia) = B (Ib) and then
             Is_Perm (Remove (A, Ia), Remove (B, Ib)))
         then
            return (Ia, Get_Witness (A, B, Ia));
         end if;
         pragma Loop_Invariant
           (for all Ka in 1 .. Ia =>
               (for all Kb in B'Range =>
                     not (A (Ka) = B (Kb) and then
                  Is_Perm (Remove (A, Ka), Remove (B, Kb)))));
      end loop;
      pragma Assert (False);
      return (A'Last, B'Last);
   end Get_Witnesses;

   function Perm_Reflexive (A, B : Nat_Array) return True_Bool is
      function Induction_Hypothesis (A, B : Nat_Array) return True_Bool with
        Pre  => Invariant (A) and then Invariant (B) and then A = B,
        Post => (if Induction_Hypothesis'Result then Is_Perm (A, B));
      pragma Annotate (GNATprove, Terminating, Induction_Hypothesis);
      function Induction_Hypothesis (A, B : Nat_Array) return True_Bool is
      begin
         if A'Length = 0 then
            return True;
         end if;
         declare
            IH : constant True_Bool :=
              Induction_Hypothesis (Remove (A, A'First), Remove (B, B'First));
         begin
            pragma Assert (IH);
            return IH;
         end;
      end Induction_Hypothesis;

   begin
      return Induction_Hypothesis (A, B);
   end Perm_Reflexive;

   function Perm_Symmetric (A, B : Nat_Array) return True_Bool is

      function Induction_Hypothesis (A, B : Nat_Array) return True_Bool with
        Pre  => Invariant (A) and then Invariant (B) and then Is_Perm (A, B),
        Post => (if Induction_Hypothesis'Result then Is_Perm (B, A));
      pragma Annotate (GNATprove, Terminating, Induction_Hypothesis);
      function Induction_Hypothesis (A, B : Nat_Array) return True_Bool is
      begin
         if A'Length = 0 then
            return True;
         end if;
         declare
            W  : constant Witnesses := Get_Witnesses (A, B);
            IH : constant True_Bool :=
              Induction_Hypothesis (Remove (A, W.Ia), Remove (B, W.Ib));
         begin
            pragma Assert (IH);
            pragma Assert (B (W.Ib) = A (W.Ia));
            return IH;
         end;
      end Induction_Hypothesis;

   begin
      return Induction_Hypothesis (A, B);
   end Perm_Symmetric;

   function Remove_Swap (A : Nat_Array; I1, I2 : Index) return True_Bool is
      A1  : constant Nat_Array := Remove (A, I1);
      A2  : constant Nat_Array := Remove (A, I2);
      A12 : constant Nat_Array := Remove (Remove (A, I1), I2 - 1);
      A21 : constant Nat_Array := Remove (Remove (A, I2), I1);
   begin
      pragma Assert (for all I in A12'Range =>
                       (if I < I1 then A12 (I) = A (I)
                        elsif I < I2 - 1 then A12 (I) = A (I + 1)
                        else A12 (I) = A (I + 2)));
      pragma Assert (for all I in A21'Range =>
                       (if I < I1 then A21 (I) = A (I)
                        elsif I < I2 - 1 then A21 (I) = A (I + 1)
                        else A21 (I) = A (I + 2)));
      return True;
   end Remove_Swap;

   function Remove_Eq (A, B : Nat_Array; I : Index) return True_Bool is
      AA  : constant Nat_Array := Remove (A, I);
      BB  : constant Nat_Array := Remove (B, I);
   begin
      pragma Assert (for all J in A'Range => A (J) = B (J));
      pragma Assert (for all J in AA'Range =>
                       (if J < I then AA (J) = A (J) and then AA (J) = B (J)
                        else AA (J) = A (J + 1) and then AA (J) = B (J + 1)));
      return True;
   end Remove_Eq;

   function Shift_Perm_L (A, B, C : Nat_Array) return True_Bool with
     Pre  => Invariant (A) and then Invariant (B) and then Invariant (C)
     and then A = C and then Is_Perm (A, B),
     Post => (if Shift_Perm_L'Result then Is_Perm (C, B));

   function Shift_Perm_L (A, B, C : Nat_Array) return True_Bool is

      function Induction_Hypothesis (A, B, C : Nat_Array) return True_Bool with
        Pre  => Invariant (A) and then Invariant (B) and then Invariant (C)
        and then A = C and then Is_Perm (A, B),
        Post => (if Induction_Hypothesis'Result then Is_Perm (C, B));
      pragma Annotate (GNATprove, Terminating, Induction_Hypothesis);
      function Induction_Hypothesis (A, B, C : Nat_Array) return True_Bool is
      begin
         if A'Length = 0 then
            return True;
         end if;

         declare
            W : constant Witnesses := Get_Witnesses (A, B);
            IH : constant True_Bool :=
              Induction_Hypothesis
                (Remove (A, W.Ia), Remove (B, W.Ib), Remove (C, W.Ia));
         begin
            pragma Assert (IH);
            return IH;
         end;
      end Induction_Hypothesis;

   begin
      return Induction_Hypothesis (A, B, C);
   end Shift_Perm_L;

   function Shift_Perm_R (A, B, C : Nat_Array) return True_Bool with
     Pre  => Invariant (A) and then Invariant (B) and then Invariant (C)
     and then C = B and then Is_Perm (A, B),
     Post => (if Shift_Perm_R'Result then Is_Perm (A, C));

   function Shift_Perm_R (A, B, C : Nat_Array) return True_Bool is
   begin
      pragma Assert (Perm_Symmetric (A, B));
      pragma Assert (Shift_Perm_L (B, A, C));
      pragma Assert (Perm_Symmetric (C, A));
      return True;
   end Shift_Perm_R;

   function Extended_Perm (A, B : Nat_Array) return True_Bool with
     Pre  => Invariant (A) and then Invariant (B) and then Is_Perm (A, B),
     Post => (if Extended_Perm'Result then
                (for all Ia in A'Range =>
                     (for some Ib in B'Range => A (Ia) = B (Ib) and then
                            Is_Perm (Remove (A, Ia), Remove (B, Ib)))));

   function Extended_Perm (A, B : Nat_Array) return True_Bool is
   begin
      if A'Length = 0 then
         return True;
      end if;
      declare
         W  : constant Witnesses := Get_Witnesses (A, B);
         AA : constant Nat_Array := Remove (A, W.Ia);
         BB : constant Nat_Array := Remove (B, W.Ib);
         IH : True_Bool := Extended_Perm (AA, BB);
      begin
         pragma Assert (IH);
         for Ia in A'Range loop
            declare
               Ib : Index;
            begin
               if Ia = W.Ia then
                  Ib := W.Ib;
               elsif Ia < W.Ia then
                  IH := Remove_Swap (A, Ia, W.Ia);
                  pragma Assert (IH);
                  Ib := Get_Witness (AA, BB, Ia);
                  IH := Shift_Perm_L (Remove (AA, Ia), Remove (BB, Ib),
                                      Remove (Remove (A, Ia), W.Ia - 1));
                  pragma Assert (IH);
                  if Ib < W.Ib then
                     IH := Remove_Swap (B, Ib, W.Ib);
                     pragma Assert (IH);
                     IH := Shift_Perm_R
                       (Remove (Remove (A, Ia), W.Ia - 1),
                        Remove (BB, Ib), Remove (Remove (B, Ib), W.Ib - 1));
                     pragma Assert (IH);
                     pragma Assert
                       (Is_Perm (Remove (Remove (A, Ia), W.Ia - 1),
                        Remove (Remove (B, Ib), W.Ib - 1)));
                     pragma Assert
                       (Is_Perm (Remove (A, Ia), Remove (B, Ib)));
                  else
                     Ib := Ib + 1;
                     IH := Remove_Swap (B, W.Ib, Ib);
                     pragma Assert (IH);
                     IH := Shift_Perm_R
                       (Remove (Remove (A, Ia), W.Ia - 1),
                        Remove (BB, Ib - 1), Remove (Remove (B, Ib), W.Ib));
                     pragma Assert (IH);
                     pragma Assert
                       (Is_Perm (Remove (Remove (A, Ia), W.Ia - 1),
                        Remove (Remove (B, Ib), W.Ib)));
                     pragma Assert
                       (Is_Perm (Remove (A, Ia), Remove (B, Ib)));
                  end if;
               else
                  IH := Remove_Swap (a, W.Ia, Ia);
                  pragma Assert (IH);
                  Ib := Get_Witness (AA, BB, Ia - 1);
                  IH := Shift_Perm_L (Remove (AA, Ia - 1), Remove (BB, Ib),
                                      Remove (Remove (A, Ia), W.Ia));
                  pragma Assert (IH);
                  if Ib < W.Ib then
                     IH := Remove_Swap (B, Ib, W.Ib);
                     pragma Assert (IH);
                     IH := Shift_Perm_R
                       (Remove (Remove (A, Ia), W.Ia),
                        Remove (BB, Ib), Remove (Remove (B, Ib), W.Ib - 1));
                     pragma Assert (IH);
                     pragma Assert
                       (Is_Perm (Remove (Remove (A, Ia), W.Ia),
                        Remove (Remove (B, Ib), W.Ib - 1)));
                     pragma Assert
                       (Is_Perm (Remove (A, Ia), Remove (B, Ib)));
                  else
                     Ib := Ib + 1;
                     IH := Remove_Swap (B, W.Ib, Ib);
                     pragma Assert (IH);
                     IH := Shift_Perm_R
                       (Remove (Remove (A, Ia), W.Ia),
                        Remove (BB, Ib - 1), Remove (Remove (B, Ib), W.Ib));
                     pragma Assert (IH);
                     pragma Assert
                       (Is_Perm (Remove (Remove (A, Ia), W.Ia),
                        Remove (Remove (B, Ib), W.Ib)));
                     pragma Assert
                       (Is_Perm (Remove (A, Ia), Remove (B, Ib)));
                  end if;
               end if;
               pragma Assert_And_Cut
                 (for some Ib in B'Range => A (Ia) = B (Ib) and then
                  Is_Perm (Remove (A, Ia), Remove (B, Ib)));
            end;
            pragma Loop_Invariant
              (for all K in 1 .. Ia =>
                 (for some Ib in B'Range => A (K) = B (Ib) and then
                  Is_Perm (Remove (A, K), Remove (B, Ib))));
         end loop;
         return IH;
      end;
   end Extended_Perm;

   function Perm_Eq (A, B : Nat_Array) return True_Bool is
      HR : True_Bool := Extended_Perm (A, B);
   begin
      return HR;
   end Perm_Eq;

   function Perm_Transitive (A, B, C : Nat_Array) return True_Bool is

      function Induction_Hypothesis (A, B, C : Nat_Array) return True_Bool with
        Pre  => Invariant (A) and then Invariant (B) and then Invariant (C)
        and then Is_Perm (A, B) and then Is_Perm (B, C),
        Post => (if Induction_Hypothesis'Result then Is_Perm (A, C));
      pragma Annotate (GNATprove, Terminating, Induction_Hypothesis);
      function Induction_Hypothesis (A, B, C : Nat_Array) return True_Bool is
      begin
         if A'Length = 0 then
            return True;
         end if;
         declare
            W   : constant Witnesses := Get_Witnesses (A, B);
            Hbc : constant True_Bool := Extended_Perm (B, C);
            Ic  : constant Index := Get_Witness (B, C, W.Ib);
         begin
            return Induction_Hypothesis
              (Remove (A, W.Ia), Remove (B, W.Ib), Remove (C, Ic));
         end;
      end Induction_Hypothesis;

   begin
      return Induction_Hypothesis (A, B, C);
   end Perm_Transitive;

   function Remove_Perm (A, B : Nat_Array; Ia, Ib : Index) return True_Bool is
      H   : True_Bool := Extended_Perm (A, B);
      Ib2 : constant Index := Get_Witness (A, B, Ia);
      AA  : constant Nat_Array := Remove (A, Ia);
      BB  : constant Nat_Array := Remove (B, Ib);
      BB2 : constant Nat_Array := Remove (B, Ib2);
      Ia2 : Index;
   begin
      if Ib = Ib2 then
         return True;
      end if;

      H := Perm_Symmetric (AA, BB2);
      pragma Assert (H);

      H := Extended_Perm (BB2, AA);
      pragma Assert (H);

      if Ib < Ib2 then
         Ia2 := Get_Witness (BB2, AA, Ib);
         H := Remove_Swap (B, Ib, Ib2);
         pragma Assert (H);
         H := Shift_Perm_L (Remove (BB2, Ib), Remove (AA, Ia2),
                            Remove (BB, Ib2 - 1));
         pragma Assert (H);
      else
         Ia2 := Get_Witness (BB2, AA, Ib - 1);
         H := Remove_Swap (B, Ib2, Ib);
         pragma Assert (H);
         H := Shift_Perm_L (Remove (BB2, Ib - 1), Remove (AA, Ia2),
                            Remove (BB, Ib2));
         pragma Assert (H);
      end if;
      H := Perm_Symmetric (BB, AA);
      return H;
   end Remove_Perm;

end Perm;
