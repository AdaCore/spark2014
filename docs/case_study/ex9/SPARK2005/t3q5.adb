package body T3Q5
is

   procedure Sort(Table : in out Array_Type)
   is
      Key : Index_Type;

      function Find_Smallest (Arr  : in Array_Type;
                              L, U : in Index_Type)
                             return Index_Type
      --# pre L <= U;
      --# return Smallest_Index =>
      --#   (for all X in Index_Type range L .. U =>
      --#      (Arr (Smallest_Index) <= Arr (X))) and
      --#     Smallest_Index in L .. U;
      is
         K : Index_Type;
      begin
         K := L;
         --# assert K = L
         --#    and (for all X in Index_Type range L .. L =>
         --#           (Arr (K) <= Arr (X)));
         if L < U then
            for I in Index_Type range L + 1 .. U loop
               if Arr (I) < Arr (K) then
                  K := I;
               end if;
               --# assert I >= L + 1 and I <= U
               --#    and L = L%     and U = U%
               --#    and L < U
               --#    and (for all X in Index_Type range L .. I =>
               --#           (Arr (K) <= Arr (X)))
               --#    and K in L .. U;
            end loop;
         end if;
         return K;
      end Find_Smallest;

      procedure Swap_Elements (T    : in out Array_Type;
                               I, J : in     Index_Type)
      --# derives T from T,I,J;
      --# post T = T~[I => T~(J);
      --#             J => T~(I)]
      --#  and Permutation (T, T~);
      is
         Temp : Contents_Type;
      begin
         Temp := T(I);
         T(I) := T(J);
         T(J) := Temp;
         --# accept W, 444, "This assumption uses the definition of a permutation:",
         --#                "If we swap any two elements, the array is a permutation",
         --#                "of itself.";
         --# assume Permutation (T~[I => T~(J); J => T~(I)], T~);
         --# end accept;
      end Swap_Elements;

   begin
      --# accept W, 444, "If two arrays are exactly the same, then they are also",
      --#                "(trivial) permutations of each other.";
      --# assume (Table = Table~) -> Permutation (Table, Table~);
      --# end accept;
      for Low in Index_Type range Index_Type'First .. Max_Table_Size - 1 loop
         Key := Find_Smallest (Table, Low, Max_Table_Size);
         if Key /= Low then
            Swap_Elements (Table, Low, Key);
         end if;
         --# assert (for all I in Index_Type range Index_Type'First .. Low =>
         --#           (Table (I) <= Table (I + 1)))
         --#    and (for all I in Index_Type range Low .. Index_Type'Last =>
         --#           (Table (Low) <= Table (I)))
         --#    and Permutation (Table, Table~);
      end loop;
   end Sort;

end T3Q5;
