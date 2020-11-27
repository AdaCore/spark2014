with Stack; use Stack;
package body List is
   pragma Spark_Mode (On);

   ------------------
   -- Reverse_List --
   ------------------

   function Reverse_List
     (L : List)
      return List
   is
      use My_Lists;
      S     : Stack.Stack := Empty_Stack;
      First : constant Integer := First_Index (L);
      Last  : constant Integer := Last_Index (L);
   begin
      return Res : List do
      clear (Res);

      for I in First .. Last loop
         Push (S, Element (L, I));
         pragma Loop_Invariant
         -- The size of the model of the stack increases with each push
           (Model.To (S)'Last = I - First + 1 and then
            -- the model of the stack contains each element of the list in order
              (for all J in First .. I =>
                   Model.To (S)(J - First + 1) = Element (L, J)));
      end loop;

      for I in First .. Last loop
         pragma Loop_Invariant
         -- The size of the List increases with each Append
           (Natural (Length (Res)) = I - First and then
            -- The size of the model of the stack decreases with each pop
            Model.To (S)'Last = Last - I + 1 and then
            -- The remaining of the model of the stack is unchanged
              (for all J in 1 .. Last - I + 1 =>
                   Model.To (S) (J) = Model.To (S'Loop_Entry) (J)) and then
            -- the Post of the subprogram is partially valid at this stage
              (for all J in First .. I - 1 =>
                   Element (Res, J) = Element (L, Last - J + First)));
         Append (Res, Top (S));
         Pop (S);
      end loop;

      end return;
   end Reverse_List;

end List;
