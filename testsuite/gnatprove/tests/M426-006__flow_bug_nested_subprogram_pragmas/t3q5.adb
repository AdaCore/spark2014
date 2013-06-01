package body T3Q5 is

   procedure Sort(Table : in out Array_Type) is
      Key        : Index_Type;

      function Find_Smallest(Arr  : Array_Type;
                             L, U : Index_Type)
                            return Index_Type
         with Pre  => (1 <= L and L < U and U <= Max_Table_Size),
              Post => L <= Find_Smallest'Result and Find_Smallest'Result <= U and
                      (for all X in L .. U => Arr (Find_Smallest'Result) <= Arr (X));

      function Find_Smallest(Arr  : Array_Type;
                             L, U : Index_Type)
                            return Index_Type
      is
         K : Index_Type;
      begin
         K := L;
         pragma Assert_And_Cut (K = L and
                                (for all X in L .. L => Arr (K) <= Arr(X)));
         if L < U then
            for I in Index_Type range L + 1 .. U loop
               if Arr (I) < Arr (K) then
                  K := I;
               end if;
               pragma Loop_Invariant(I >= L + 1 and I <= U and
                                     L = L'Loop_Entry and U = U'Loop_Entry and
                                     L < U and
                                     (for all X in L .. I => Arr (K) <= Arr (X)) and
                                     K in L .. U);
            end loop;
         end if;
         return K;
      end Find_Smallest;

      procedure Swap_Elements(T    : in out Array_Type;
                              I, J : in     Index_Type)
         with Post => (T(I) = T'Old(J) and then T(J) = T'Old(I) and then
                       (for all X in Index_Type => (if (X /= I and X /= J) then T(X) = T'Old(X))) and then
                       Perm (T, T'Old));

      procedure Swap_Elements(T    : in out Array_Type;
                              I, J : in     Index_Type)
      is
         T_Old : Array_Type := T;
         Temp  : Contents_Type;
      begin
         Temp := T(I); T(I) := T(J); T(J) := Temp;
         pragma Assume (Perm (T, T_Old));
      end Swap_Elements;

   begin -- Sort
      for Low in Index_Type range 1 .. Max_Table_Size - 1 loop
         Key := Find_Smallest(Table, Low, Max_Table_Size);
         if Key /= Low then
            Swap_Elements(Table, Low, Key);
         end if;
         pragma Loop_Invariant ((for all X in 1 .. Low => Table (X) <= Table (X + 1)) and then
                                (for all X in Low .. Max_Table_Size => Table (Low) <= Table (X)) and then
                                Perm (Table, Table'Loop_Entry));
      end loop;
   end Sort;

end T3Q5;

