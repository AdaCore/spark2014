-- Factorial computation

package body Factorial
with SPARK_Mode
is

   function Fact (X : Integer) return Integer is
   begin
      return Result : Integer do
         Result := 1;
         for I in 2 .. X loop
            Result := Result * I;
            pragma Loop_Invariant (Result = Mathematical_Factorial (I));
         end loop;
      end return;
   end Fact;

end Factorial;
