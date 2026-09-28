package body Linked_Lists is

   function Contains_Value (M : Memory; X : Natural; V : Integer) return Boolean
   is
      C : Natural := X;
   begin
      while C /= 0 loop
         pragma Loop_Invariant (C in M'Range and then Is_Acyclic (C, M));
         pragma Loop_Invariant (Reachable_Set (C, M) <= Reachable_Set (X, M));
         pragma Loop_Invariant
           (for all I of Reachable_Set (X, M) =>
              (if M (I).Value = V then Contains (Reachable_Set (C, M), I)));
         pragma Loop_Variant (Decreases => Length (Reachable_Set (C, M)));

         if M (C).Value = V then
            return True;
         end if;
         C := M (C).Next;
      end loop;
      pragma Assert (Is_Empty (Reachable_Set (C, M)));
      return False;
   end Contains_Value;

end Linked_Lists;
