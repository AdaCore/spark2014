package body Show_Composite_Types_Shortcoming is

   procedure Init_Loop (A : out T) is
   begin
      for I in A'Range loop
         if I = A'First then
            A (I) := 0;
         else
            A (0) := 0;
         end if;
      end loop;
      --  flow analysis doesn't know that A is initialized
   end Init_Loop;

end Show_Composite_Types_Shortcoming;
