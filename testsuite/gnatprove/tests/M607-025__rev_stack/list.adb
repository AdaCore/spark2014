with Stack; use Stack;
package body List is

   ------------------
   -- Reverse_List --
   ------------------

   function Reverse_List
     (L : List)
      return List
   is
      S : Stack.Stack;
      Res : List;
   begin
      for I in T loop
         Push (S, Element (L, I));
      end loop;

      for I in T loop
         Append (Res, Top (S));
         Pop (S);
         pragma Loop_Invariant (for all J in 1..I => Element (Res, J) = Element (L, T'Last - J + 1));
      end loop;

      return Res;
   end Reverse_List;

end List;
