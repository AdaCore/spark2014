package body Binary_Search
  with SPARK_Mode
is

   function Search (A : Ar; I : Integer) return Opt_Index is
      Left  : Index;
      Right : Index;
      Med   : Index;
   begin
      if Empty (A) then
         return No_Index;
      end if;

      Left  := A'First;
      Right := A'Last;

      if Left = Right and A (Left) = I then
         return Left;
      elsif A (Left) > I or A (Right) < I then
         return No_Index;
      end if;

      while Left <= Right loop
         pragma Loop_Variant (Increases => Left, Decreases => Right);
         pragma Loop_Invariant (Left in A'Range and Right in A'Range);
         pragma Loop_Invariant
           (for all Index in A'First .. Left - 1 => A (Index) < I);
         pragma Loop_Invariant
           (for all Index in A'Range =>
              (if Index > Right then I < A (Index)));

         Med := Left + (Right - Left) / 2;

         if A (Med) < I then
            Left := Med + 1;
         elsif A (Med) > I then
            Right := Med - 1;
         else
            return Med;
         end if;
      end loop;
      pragma Assert (for all Index in A'Range => A (Index) /= I);

      return No_Index;
   end Search;

end Binary_Search;
