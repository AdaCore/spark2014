with Stack; use Stack;
package body List is 

   ------------------
   -- Reverse_List --
   ------------------

   function Reverse_List
     (L : List)
      return List
   is
      S     : Stack.Stack;
      Res   : List;
      First : constant Integer := First_Index (L);
      Last  : constant Integer := Last_Index (L);
   begin
      clear (Res);
      
      for I in First .. Last loop
         Push (S, Element (L, I));
         pragma Loop_Invariant
         -- The size of the model of the stack increases with each push
           (Model.To (S)'Last = I - First + 1 and then
            -- the model of the stack contains each element of the list in order
              (for all J in First .. I => Model.To (S)(J) = Element (L, J)));
      end loop;

      for I in  First .. Last loop
         Append (Res, Top (S));
         Pop (S);
         pragma Loop_Invariant
         -- The size of the List increases with each Append
           (Natural (Length (Res)) = I - First + 1 and then
            -- The size of the model of the stack decreases with each pop
            Model.To (S)'Last = Last - I and then
            -- The remaining of the model of the stack is unchanged
              (for all J in First .. Last - I =>
                   Model.To (S) (J) = Model.To (S'Loop_Entry)(J)) and then
            -- the Post of the subprogram is partially valid at this stage
              (for all J in First .. I =>
                   Element (Res, J) = Element (L, Last_Index (L) - J + 1)));
      end loop;

      return Res;
   end Reverse_List;

end List;
