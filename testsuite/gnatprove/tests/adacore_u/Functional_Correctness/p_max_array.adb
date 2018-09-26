package body P_Max_Array with SPARK_Mode is

   function Max_Array_1 (A, B : Nat_Array) return Nat_Array is
      R : Nat_Array (A'Range);
      J : Integer := B'First;
   begin
      for I in A'Range loop
         pragma Loop_Invariant (J in B'Range);
         pragma Loop_Invariant (J = I - A'First + B'First);
         if A (I) > B (J) then
            R (I) := A (I);
         else
            R (I) := B (J);
         end if;
         J := J + 1;
      end loop;
      return R;
   end Max_Array_1;

   function Max_Array_2 (A, B : Nat_Array) return Nat_Array is
      R : Nat_Array (A'Range) := (others => 0);
      J : Integer := B'First;
   begin
      for I in A'Range loop
         pragma Loop_Invariant (J in B'Range);
         pragma Loop_Invariant (J = I - A'First + B'First);
         pragma Loop_Invariant
           (for all K in A'First .. (I - 1) =>
                (if A (K) > B (K - A'First + B'First) then
                     R (K) = A (K)
                 else R (K) = B (K - A'First + B'First)));
         if A (I) > B (J) then
            R (I) := A (I);
         else
            R (I) := B (J);
         end if;
         J := J + 1;
      end loop;
      return R;
   end Max_Array_2;

   procedure Max_Array_3 (A : in out Nat_Array; B : Nat_Array) is
      J : Integer := B'First;
   begin
      for I in A'Range loop
         pragma Loop_Invariant (J in B'Range);
         pragma Loop_Invariant (J = I - A'First + B'First);
         pragma Loop_Invariant
           (for all K in A'First .. (I - 1) =>
                (if A'Loop_Entry (K) > B (K - A'First + B'First) then
                     A (K) = A'Loop_Entry (K)
                 else A (K) = B (K - A'First + B'First)));
         pragma Loop_Invariant
           (for all K in I .. A'Last => A (K) = A'Loop_Entry (K));
         if A (I) < B (J) then
            A (I) := B (J);
         end if;
         J := J + 1;
      end loop;
   end Max_Array_3;

end P_Max_Array;
