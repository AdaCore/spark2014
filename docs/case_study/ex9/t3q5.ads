package T3Q5 is

   Max_Table_Size : constant := 100;
   type Base_Index_Type is range 0..Max_Table_Size;
   --# assert Base_Index_Type'Base is Integer;
   subtype Index_Type is Base_Index_Type range 1..Max_Table_Size;
   type Contents_Type is range -1000 .. 1000;
   type Array_Type is array(Index_Type) of Contents_Type;

   function Ordered(A : Array_Type; L,U : Index_Type)
                   return Boolean is
      (for all I in Index_Type range L..U => (for all J in Index_Type range I..U => (A(I) <= A(J))));
   --# function Ordered(A : Array_Type; L,U : Index_Type)
   --# return Boolean;
   --# return (for all I in Index_Type range L..U => (for all J in Index_Type range I..U => (A(I) <= A(J))));

   function Perm(A, B : Array_Type) return Boolean is
      ((for some I in Index_Type => (for some J in Index_Type => (B(I) = A(J) and B(J) = A(I) and
                                                                    (for all N in Index_Type => (if (N /= I and N /= J) then A(N) = B(N))))))); -- or
   -- (for some C in Array_Type => (Perm (A, C) and Perm (B, C))));
   --# function Perm(A, B : Array_Type) return Boolean;
   --  return ((for some I in Index_Type => (for some J in Index_Type => (B = A[I => A(J); J => A(I)]))) or
   --            (for some C in Array_Type => (Perm (A, C) and Perm (B, C))));

   procedure Sort(Table : in out Array_Type)
     with Post => (Ordered(Table,1,Max_Table_Size) and
                     Perm(Table,Table'Old));
   --# derives Table from Table;
   --# post Ordered(Table,1,Max_Table_Size) and
   --#   Perm(Table,Table~);

end T3Q5;
