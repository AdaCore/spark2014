package body Binary_Search is  

   function Search (A : Ar ; I : Integer) return T is
      Left  : U;
      Right : U;
      Med   : U;
   begin
      if A'Length = 0 then
         return 0;
      end if;

      Left  := Ar'First;
      Right := Ar'Last;

      if A (Left) > I or else A (Right) < I then
         return 0;
      end if;

      while Left < Right loop
         pragma Loop_Invariant
           ((for all Index in A'First .. Left => A (Index) <= I)
              and then (for all Index in A'First .. Left => I <= A (Index)));
         pragma Loop_Variant (Decreases => Right - Left);
         Med := Left + (Right - Left) / 2;
         if A (Med) < I then
            Left := Med;
         elsif A (Med) > I then
            Right := Med;
         else
            return Med;
         end if;
      end loop;
      return 0;
   end Search;

end Binary_Search;
