package body T3Q5 is

   function Partitioned(A : Array_Type;
                        L, M, U : Index_Type) return Boolean is
      (for all I in Index_Type range L..M => (for all J in Index_Type range M+1..U => (A(I) <= A(J))));
   --# function Partitioned(A : Array_Type;
   --#                      L, M, U : Index_Type) return Boolean;
   --# return (for all I in Index_Type range L..M => (for all J in Index_Type range M+1..U => (A(I) <= A(J))));
   --| This predicate asserts that every element of A within
   --| L..M is less than or equal to every element in M+1..U.

   procedure Sort(Table : in out Array_Type) is
      Key : Index_Type;
      Table_Tilde : Array_Type := Table;

      function The_Smallest(A : Array_Type;
                            L,U : Index_Type) return Index_Type
        with Post => (U <= The_Smallest'Result and The_Smallest'Result <= U and
                        (for all N in Index_Type range L .. U => (A(The_Smallest'Result) <= A(N))) and
                        (for some N in Index_Type range L .. U => (A(The_Smallest'Result) = A(N))));
      --# function The_Smallest(A : Array_Type;
      --#                       L,U : Index_Type) return Index_Type;
      --# return Small => (U <= Small and Small <= U and
      --#                    (for all N in Index_Type range L .. U => (A(Small) <= A(N))) and
      --#                    (for some N in Index_Type range L .. U => (A(Small) = A(N))));

      function The_Smallest(A : Array_Type;
                            L,U : Index_Type) return Index_Type is
         Result : Index_Type;
      begin
         for Result in Index_Type loop
            exit when (U <= Result and Result <= U and
                         (for all N in Index_Type range L .. U => (A(Result) <= A(N))) and
                         (for some N in Index_Type range L .. U => (A(Result) = A(N))));
         end loop;
         return Result;
      end The_Smallest;

      function Find_Smallest(Arr : Array_Type; L,U: Index_Type)
                            return Index_Type
        with Pre => (1 <= L and L < U and U <= Max_Table_Size),
        Post => (Find_Smallest'Result = The_Smallest(Arr,L,U));

      function Find_Smallest(Arr : Array_Type; L,U: Index_Type)
                            return Index_Type
        --# pre 1 <= L and L < U and U <= Max_Table_Size;
        --# return The_Smallest(Arr,L,U);
      is
         K : Index_Type;
      begin
         K := L;
         for I in Index_Type range L+1..U loop
            pragma Loop_Invariant (1 <= L and L+1 <= I and
                             I <= U and U <= Max_Table_Size and
                             K in Index_Type and
                             K = The_Smallest(Arr,L,I-1));
            if Arr(I) <= Arr(K) then
               K := I;
            end if;
            --# assert 1 <= L and L+1 <= I and
            --#   I <= U and U <= Max_Table_Size and
            --#   U = U% and K in Index_Type and
            --#   K = The_Smallest(Arr,L,I);
         end loop;
         return K;
      end Find_Smallest;

      procedure Swap_Elements(T : in out Array_Type;
                              I, J : in Index_Type)
        with Post => (T(I) = T'Old(J) and T(J) = T'Old(I) and
                        (for all N in Index_Type => (if (N /= I and N /= J) then T(N) = T'Old(N))) and
        Perm(T,T'Old));

      procedure Swap_Elements(T : in out Array_Type;
                              I, J : in Index_Type)
        --# derives T from T,I,J;
        --# post T = T~[I => T~(J); J => T~(I)] and Perm(T,T~);
      is
         Temp : Contents_Type;
      begin
         Temp := T(I); T(I) := T(J); T(J) := Temp;
      end Swap_Elements;

   begin -- Sort
      for Low in Index_Type range 1 .. Max_Table_Size-1 loop
         pragma Loop_Invariant (1 <= Low and Low <= Max_Table_Size-1 and
                          (if Low /= Index_Type'First then (Ordered(Table,1,Low-1) and
                                                              Partitioned(Table,1,Low-1,Max_Table_Size))) and
           Perm(Table,Table_Tilde));
         Key := Find_Smallest(Table,Low,Max_Table_Size);
         if Key /= Low then
            Swap_Elements(Table,Low,Key);
         end if;
         --# assert 1 <= Low and Low <= Max_Table_Size-1 and
         --#      Ordered(Table,1,Low) and
         --#      Partitioned(Table,1,Low,Max_Table_Size) and
         --#      Perm(Table,Table~);
      end loop;
   end Sort;

end T3Q5;
