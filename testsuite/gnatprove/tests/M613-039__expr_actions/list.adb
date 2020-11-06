pragma SPARK_Mode;

with Stack; use Stack;
package body List is
   use Stack.Model;

   ------------------
   -- Reverse_List --
   ------------------

   function Reverse_List
     (L : List)
      return List
   is
      pragma Spark_Mode;
      S   : Stack.Stack;
      First : constant Integer := First_Index (L);
      Last  : constant Integer := Last_Index (L);
   begin
      return Res : List do

      for I in First .. Last loop
         Push (S, Element (L, I));
         pragma Loop_Invariant
           (Model.To (S)'Last = I - First + 1 and then
            (for all J in First .. I => Model.To (S)(J) = Element (L, J)));
      end loop;

      for I in First .. Last loop
         Append (Res, Top (S));
         Pop (S);
         pragma Loop_Invariant
           (Model.To (S)'Last = Last - I and then
              (Model.To (S) (First .. Last - I)
                = Model.To (S'Loop_Entry) (First .. Last - I)) and then
            (for all J in First .. I =>
              Element (Res, J) = Element (L, Last_Index (L) - J + 1)));
      end loop;

      end return;
   end Reverse_List;

end List;
