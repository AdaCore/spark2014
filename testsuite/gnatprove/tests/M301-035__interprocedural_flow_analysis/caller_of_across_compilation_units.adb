with Across_Compilation_Units; use Across_Compilation_Units;

package body Caller_Of_Across_Compilation_Units is
   function Min (X, Y: Natural) return Natural is
   begin
      if X < Y then
         return X;
      else
         return Y;
      end if;
   end Min;

   function Coprime (X, Y: Natural) return Boolean is
   begin
      if Prime (X) or else Prime (Y) then
         return True;
      end if;

      for I in 2 .. Min (X, Y) loop
         if (X mod I) = 0 and then (Y mod I) = 0 then
            return False;
         end if;
      end loop;
      return True;
   end Coprime;
end Caller_Of_Across_Compilation_Units;
