package T3Q5
is

   Max_Table_Size : constant := 100;

   type Base_Index_Type is range 0 .. Max_Table_Size;
   subtype Index_Type is Base_Index_Type range 1 .. Max_Table_Size;

   type Contents_Type is range -1000 .. 1000;

   type Array_Type is array (Index_Type) of Contents_Type;

   --# function Ordered (A : in Array_Type) return Boolean;
   --# return for all I in Index_Type range Index_Type'First .. Index_Type'Pred (Index_Type'Last) =>
   --#   (A (I) <= A (I + 1));

   --# function Permutation (A, B : in Array_Type) return Boolean;

   procedure Sort (Table : in out Array_Type);
   --# derives Table from Table;
   --# post Ordered (Table) and Permutation (Table, Table~);

end T3Q5;
