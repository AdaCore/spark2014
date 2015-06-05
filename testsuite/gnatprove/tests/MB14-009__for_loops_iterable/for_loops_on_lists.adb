package body For_Loops_On_Lists with SPARK_Mode is

   function Search_0_For_In (L : List) return Cursor is
   begin
      for Cu in L loop
         pragma Loop_Invariant
           (for all Cu2 in First_To_Previous (L, Cu) => Element (L, Cu2) /= 0);
         if Element (L, Cu) = 0 then
            return Cu;
         end if;
      end loop;
      return No_Element;
   end Search_0_For_In;

   function Contains_0_For_Of (L : List) return Boolean is
   begin
      for E of L loop
         if E = 0 then
            return True;
         end if;
      end loop;
      return False;
   end Contains_0_For_Of;
end For_Loops_On_Lists;
