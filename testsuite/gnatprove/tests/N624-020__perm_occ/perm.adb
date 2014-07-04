package body Perm with SPARK_Mode is

   procedure Occ_Eq (A, B : Nat_Array; E : Natural) is
      begin
      if A'Length = 0 then
         return;
      end if;

      Occ_Eq (Remove_Last (A), Remove_Last (B), E);

      if A (A'Last) = E then
         pragma Assert (B (B'Last) = E);
      else
         pragma Assert (B (B'Last) /= E);
      end if;
   end Occ_Eq;

   function Set (A : Nat_Array; I : Index; V : Natural) return Nat_Array is
      Result : Nat_Array := A;
   begin
      Result (I) := V;
      return Result;
   end Set;


   procedure Occ_Set (A : Nat_Array; I : Index; V, E : Natural) is
   begin
      if A'Length = 0 then
         return;
      end if;

      if I = A'Last then
         Occ_Eq (Remove_Last (A), Remove_Last (Set (A, I, V)), E);
      else
         Occ_Set (Remove_Last (A), I, V, E);
         Occ_Eq (Remove_Last (Set (A, I, V)),
                 Set (Remove_Last (A), I, V), E);
      end if;
   end Occ_Set;

end Perm;
