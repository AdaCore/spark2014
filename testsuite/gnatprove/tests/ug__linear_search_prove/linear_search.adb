package body Linear_Search
  with SPARK_Mode
is

   function Search
     (A   : Arr;
      Val : Element) return Search_Result
   is
      Pos : Index := A'First;
      Res : Search_Result;
   begin
      while Pos < A'Last loop
         pragma Loop_Variant (Increases => Pos);

         if A(Pos) = Val then
            Res := (Found    => True,
                    At_Index => Pos);
            return Res;
         end if;

         Pos := Pos + 1;
      end loop;

      Res := (Found => False);
      return Res;
   end Search;

end Linear_Search;
