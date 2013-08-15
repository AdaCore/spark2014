--  Specification of "Sort"
--     Ordered(Table, 1, Max_Table_Size) and
--     Perm(Table, Table'Old)

--  Where "ordered" defines an ordering relationship
--  and "perm" defines set equivalence.

package Sorting
is
   Max_Table_Size : Natural := 9;
   subtype Base_Index_Type is Natural range 0 .. Max_Table_Size;
   subtype Index_Type      is Base_Index_Type range 1 .. Max_Table_Size;
   subtype Contents_Type   is Integer range -1000 .. 1000;
   type    Array_Type      is array (Index_Type) of Contents_Type;

   function Ordered (A    : Array_Type;
                     L, U : Index_Type) return Boolean;
   pragma Precondition  (L < U);
   pragma Postcondition (Ordered'Result =
                           (for all I in Index_Type range L .. U - 1 =>
                               A (I) <= A (I + 1)));
   --  Returns true if all elements in range L .. U of array A are
   --  in ascending order and false otherwise.



   function Number_Of_Occurrences (A    : Array_Type;
                                   L, U : Index_Type;
                                   N    : Contents_Type) return Base_Index_Type;
   pragma Precondition  (L <= U);
   pragma Postcondition (if L = U and A (L) = N then
                            Number_Of_Occurrences'Result = 1
                         elsif L = U and A (L) /= N then
                            Number_Of_Occurrences'Result = 0
                         elsif L < U and A (L) = N then
                            Number_Of_Occurrences'Result =
                              Number_Of_Occurrences (A, L + 1, U, N) + 1 and
                            Number_Of_Occurrences'Result <= U - L + 1
                         else
                            Number_Of_Occurrences'Result =
                              Number_Of_Occurrences (A, L + 1, U, N) and
                            Number_Of_Occurrences'Result <= U - L + 1);
   --  Returns the number of times that number "N" appears in the range L .. U
   --  of array A. Both the implementation and the postcondition are recursive.



   function Perm (A, B : Array_Type) return Boolean;
   pragma Postcondition (Perm'Result =
                           (for all I in Index_Type =>
                              Number_Of_Occurrences
                                (A, 1, Max_Table_Size, A (I)) =
                              Number_Of_Occurrences
                                (B, 1, Max_Table_Size, A (I))));
   --  Returns true if every element in array A appears the exact same number
   --  of times both in array A and in array B. Otherwise it returns false.

   procedure Sort (Table : in out Array_Type);
   pragma Postcondition (Ordered (Table, 1, Max_Table_Size) and
                         Perm (Table, Table'Old));
   --  Sorts Table in an ascending order. The resulting array is a permutation
   --  of the initial array.
end Sorting;
