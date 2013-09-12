package T3Q5 is 

   Max_Table_Size : constant := 100;
   type Base_Index_Type is range 0..Max_Table_Size;
   --# assert Base_Index_Type'Base is Integer;
   subtype Index_Type is Base_Index_Type range 1..Max_Table_Size;
   type Contents_Type is range -1000 .. 1000;
   type Array_Type is array(Index_Type) of Contents_Type;


   function Ordered(A : Array_Type; L, U : Index_Type) return Boolean is
      (for all I in Index_Type range L..U-1 => (A(I) <= A(I+1)))
      with Convention => Ghost;
   --# function Ordered (A : in Array_Type) return Boolean;
   --# return for all I in Index_Type range Index_Type'First .. Index_Type'Pred (Index_Type'Last) =>
   --#   (A (I) <= A (I + 1));


   function Perm(A, B : Array_Type) return Boolean
      with Convention => Ghost,
           Post       => (if A = B then Perm'Result),
           Import;



       --  A = B or else
       --  (for some I in Index_Type =>
       --     (for some J in Index_Type => (B(I) = A(J) and
       --                                   B(J) = A(I) and
       --                                   (for all N in Index_Type =>
       --                                      (if (N /= I and N /= J) then A(N) = B(N)))))));

   --  function Perm_Trans_Lemma (A, B, C : Array_Type) return Boolean is
   --     (if Perm(A, B) and then Perm(B, C) then Perm(A, C))
   --     with Convention => Ghost;
   --  The previously mentioned expression function used to be the following user rule.
   --  permutation_is_transitive(1):
   --       permutation(A, C)
   --       may_be_deduced_from
   --       [permutation(A, B),
   --        permutation(B, C),
   --        goal(checktype(A, array_type)),
   --        goal(checktype(B, array_type)),
   --        goal(checktype(C, array_type))].

   procedure Sort(Table : in out Array_Type)
      with Post => (Ordered (Table, 1, Max_Table_Size) and
                    Perm (Table, Table'Old));
   --# derives Table from Table;
   --# post Ordered(Table,1,Max_Table_Size) and
   --#   Perm(Table,Table~);

end T3Q5;
