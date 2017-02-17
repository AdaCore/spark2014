package body Stack is

   procedure Push (T : in out Stack_T; S : in out Size_T; Value : Natural) is
      N : constant Size_T := Size (T);
   begin
      T (N + 1) := Value;
      S := Size (T);
   end Push;

   function Size (T : Stack_T) return Size_T is
   begin
      for Index in T'Range loop
         pragma Loop_Invariant (for all I in Index_T'first .. Index - 1 =>
                          T (I) /= No_Element);
         if T (Index) = No_Element then
            return Index - 1;
         end if;
      end loop;
      return Index_T'Last;
   end Size;

end Stack;












