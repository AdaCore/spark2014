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
         pragma Loop_Invariant (Left in A'Range and Right in A'Range);
         pragma Loop_Invariant
           (for all Index in A'First .. Left - 1 => A (Index) < I);
         pragma Loop_Invariant
           (for all Index in A'Range =>
              (if Index > Right then I < A (Index)));

         Med := Left + (Right - Left) / 2;

         pragma Assert
           (for all I1 in A'Range =>
              (for all I2 in I1 .. A'Last => A (I1) <= A (I2)));

         if A (Med) < I then
            Left := Med + 1;
            pragma Assert (for all I1 in A'First .. Med => A (I1) <= A (Med));
         elsif A (Med) > I then
            Right := Med - 1;
            pragma Assert (Med in A'Range);
            pragma Assert (for all I2 in Med .. A'Last => A (Med) <= A (I2));
         else
            return Med;
         end if;
      end loop;

      return No_Index;
   end Search;

end Binary_Search;
