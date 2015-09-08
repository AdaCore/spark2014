pragma SPARK_Mode(On);

package body Various is

   function Search_For_Zero(Values : Integer_Array) return Index_Type is
   begin
      for J in Index_Type loop
         if Values(J) = 0 then
            return J;
         end if;
      end loop;
      raise Program_Error;
   end Search_For_Zero;

   X : Positive := 1;
   Y : Positive := 2;

   procedure Silly is
   begin
      pragma Assert((X+Y)/2 in Positive);
      X := X/2 + 1;
   end Silly;

end Various;
