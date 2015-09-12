pragma SPARK_Mode(On);

package body Utility is
   pragma Assertion_Policy(Ignore);

   function Search_For_Zero (Values : Integer_Array) return Index_Type is
   begin
      for Index in Index_Type loop
         if Values (Index) = 0 then
            return Index;
         end if;
         pragma Loop_Invariant
           (for some J in Index + 1 .. Index_Type'Last => Values (J) = 0);
      end loop;
      raise Program_Error;
   end Search_For_Zero;

end Utility;
