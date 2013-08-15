package body Sorting
is
   -------------
   -- Ordered --
   -------------
   function Ordered (A    : Array_Type;
                     L, U : Index_Type) return Boolean
   is
   begin
      for I in L .. U - 1 loop
         if A (I) > A (I + 1) then
            return False;
         end if;
         pragma Loop_Invariant (for all N in L .. I => A (N) <= A (N + 1));
      end loop;
      return True;
   end Ordered;

   ---------------------------
   -- Number_Of_Occurrences --
   ---------------------------
   function Number_Of_Occurrences (A    : Array_Type;
                                   L, U : Index_Type;
                                   N    : Contents_Type) return Base_Index_Type
   is
   begin
      if L = U and A (L) = N then
         return 1;
      elsif L = U and A (L) /= N then
         return 0;
      elsif L < U and A (L) = N then
         return Number_Of_Occurrences (A, L + 1, U, N) + 1;
      else
         return Number_Of_Occurrences (A, L + 1, U, N);
      end if;
   end Number_Of_Occurrences;

   ----------
   -- Perm --
   ----------
   function Perm (A, B : Array_Type) return Boolean
   is
   begin
      for I in Index_Type loop
         if Number_Of_Occurrences (A, 1, Max_Table_Size, A (I)) /=
           Number_Of_Occurrences (B, 1, Max_Table_Size, A (I))
         then
            return False;
         end if;
         pragma Loop_Invariant
           (for all N in Index_Type range 1 .. I =>
              Number_Of_Occurrences (A, 1, Max_Table_Size, A (N)) =
              Number_Of_Occurrences (B, 1, Max_Table_Size, A (N)));
      end loop;
      return True;
   end Perm;

   ----------
   -- Sort --
   ----------
   procedure Sort (Table : in out Array_Type)
   is
      function Find_Smallest (Arr  : Array_Type;
                              L, U : Index_Type) return Index_Type;
      pragma Precondition  (L <= U);
      pragma Postcondition (Find_Smallest'Result in L .. U and
                              (for all I in L .. U =>
                                 Arr(Find_Smallest'Result) <= Arr(I)));

      function Find_Smallest (Arr  : Array_Type;
                              L, U : Index_Type) return Index_Type
      is
         Smallest : Index_Type;
      begin
         Smallest := L;
         for I in Index_Type range L .. U loop
            if Arr (Smallest) > Arr (I) then
               Smallest := I;
            end if;
            pragma Loop_Invariant (Smallest in L .. I and
                                     (for all N in L .. I =>
                                        Arr (Smallest) <= Arr (N)));
         end loop;
         return Smallest;
      end Find_Smallest;


      procedure Swap_Elements (T    : in out Array_Type;
                               I, J : in     Index_Type);
      pragma Postcondition (T (I) = T'Old (J) and
                            T (J) = T'Old (I) and
                            (for all N in Index_Type =>
                               (if N /= I and N /= J then T(N) = T'Old(N))) and
                            Perm (T, T'Old));

      procedure Swap_Elements (T    : in out Array_Type;
                               I, J : in Index_Type)
      is
         Temp  : Contents_Type;
         T_Old : constant Array_Type := T;
      begin
         Temp  := T (I);
         T (I) := T (J);
         T (J) := Temp;
         pragma Assume (Perm (T, T_Old));  --  Assumption is not proven.
      end Swap_Elements;

      Key       : Index_Type;
      Table_Old : constant Array_Type := Table;
   begin -- Sort
      for Low in Index_Type range 1 .. Max_Table_Size loop
         Key := Find_Smallest (Table, Low, Max_Table_Size);
         if Key /= Low then
            Swap_Elements (Table, Low, Key);
         end if;
         pragma Loop_Invariant (Ordered (Table, 1, Low) and
                                Perm (Table, Table_Old));
      end loop;
   end Sort;
end Sorting;

