with Memory_Lists; use Memory_Lists;
use Memory_Lists.Index_Sets;
use Memory_Lists.Lists;

package Linked_Lists is

   function Contains_Value (M : Memory; X : Natural; V : Integer) return Boolean
   with
     Pre  =>
       Valid_Memory (M) and then X in M'Range | 0 and then Is_Acyclic (X, M),
     Post =>
       Contains_Value'Result =
         (for some I of Reachable_Set (X, M) => M (I).Value = V);
   --  Search for V in the list starting at X in M

end Linked_Lists;
