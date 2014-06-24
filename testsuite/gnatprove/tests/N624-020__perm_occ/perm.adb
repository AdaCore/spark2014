package body Perm with SPARK_Mode is

   function Remove_Last (A : Nat_Array) return Nat_Array is
   begin
      return A (A'First .. A'Last -1);
   end Remove_Last;

   function Occ_Eq (A, B : Nat_Array; E : Natural) return True_Bool is

      function Induction_Hypothesis (A, B : Nat_Array; E : Natural)
                                     return True_Bool with
        Pre  => A = B,
        Post => (if Induction_Hypothesis'Result then Occ (A, E) = Occ (B, E));

      function Induction_Hypothesis (A, B : Nat_Array; E : Natural)
                                     return True_Bool is
      begin
         if A'Length = 0 then
            return True;
         end if;

         declare
            IH : constant True_Bool :=
              Induction_Hypothesis (Remove_Last (A), Remove_Last (B), E);
         begin
            if A (A'Last) = E then
               pragma Assert (B (B'Last) = E);
               return IH;
            else
               pragma Assert (B (B'Last) /= E);
               return IH;
            end if;
         end;
      end Induction_Hypothesis;

   begin
      return Induction_Hypothesis (A, B, E);
   end Occ_Eq;

   function Set (A : Nat_Array; I : Index; V : Natural) return Nat_Array is
      Result : Nat_Array := A;
   begin
      Result (I) := V;
      return Result;
   end Set;


   function Occ_Set (A : Nat_Array; I : Index; V, E : Natural) return True_Bool is

      function Induction_Hypothesis (A : Nat_Array; I : Index; V, E : Natural)
                                     return True_Bool with
        Pre  => I in A'Range,
        Post =>
          (if Induction_Hypothesis'Result then
             (if V = A (I) then Occ (Set (A, I, V), E) = Occ (A, E)
                  elsif V = E then Occ (Set (A, I, V), E) = Occ (A, E) + 1
                  elsif A (I) = E then Occ (Set (A, I, V), E) = Occ (A, E) - 1
                  else Occ (Set (A, I, V), E) = Occ (A, E)));

      function Induction_Hypothesis (A : Nat_Array; I : Index; V, E : Natural)
                                     return True_Bool is
      begin
         if A'Length = 0 then
            return True;
         end if;

         if I = A'Last then
            declare
               HE : True_Bool :=
                 Occ_Eq (Remove_Last (A), Remove_Last (Set (A, I, V)), E);
            begin
               return HE;
            end;
         else
            declare
               IH : constant True_Bool :=
                 Induction_Hypothesis (Remove_Last (A), I, V, E);
               HE : constant True_Bool :=
                 Occ_Eq (Remove_Last (Set (A, I, V)),
                         Set (Remove_Last (A), I, V), E);
            begin
               return IH and HE;
            end;
         end if;
      end Induction_Hypothesis;

   begin
      return Induction_Hypothesis (A, I, V, E);
   end Occ_Set;

end Perm;
