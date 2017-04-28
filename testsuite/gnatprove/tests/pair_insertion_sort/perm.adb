package body Perm with SPARK_Mode is

   procedure Occ_Eq (A, B : Arr; E : Integer)
   with
     Global => null,
     Pre  => A = B,
     Post => Occ (A, E) = Occ (B, E);

   procedure Occ_Eq (A, B : Arr; E : Integer) is
   begin
      if A'Length = 0 then
         return;
      end if;

      if A (A'Last) = E then
         pragma Assert (B (B'Last) = E);
      else
         pragma Assert (B (B'Last) /= E);
      end if;

      Occ_Eq (Remove_Last (A), Remove_Last (B), E);
   end Occ_Eq;

   procedure Occ_Set (A : Arr; I : Index; V, E : Integer; R : Arr) is
      B : Arr:= Remove_Last (A);
   begin
      if A'Length = 0 then
         return;
      end if;

      if I = A'Last then
         Occ_Eq (B, Remove_Last (R), E);
      else
         B (I) := V;
         Occ_Eq (Remove_Last (R), B, E);
         Occ_Set (Remove_Last (A), I, V, E, B);
      end if;
   end Occ_Set;

end Perm;
