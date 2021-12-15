package body Linear_Search
  with SPARK_Mode
is

   function Search (A : Ar; I : Integer) return Opt_Index is
   begin
      for Pos in A'Range loop
         if A (Pos) = I then
            return Pos;
         end if;

         pragma Loop_Invariant (for all K in A'First .. Pos => A (K) /= I);
      end loop;

      return No_Index;
   end Search;

end Linear_Search;
