with Stack; use Stack;
package body List is

   ------------------
   -- Reverse_List --
   ------------------

   function Reverse_List
     (L : List)
      return List
   is
      S   : Stack.Stack (Integer (Length (L)));
   begin
      return Res : List do
      for I in First_Index (L) .. Last_Index (L) loop
         Push (S, Element (L, I));
      end loop;

      for I in First_Index (L) .. Last_Index (L) loop
         Append (Res, Top (S));
         Pop (S);
         pragma Loop_Invariant (for all J in 1..I => Element (Res, J) = Element (L, Last_Index (L) - J + 1));
      end loop;

      end return;
   end Reverse_List;

end List;
