package body Search is

   function Linear_Search (A : Arr; Val : Element) return Search_Result is
      Pos    : Index'Base := A'First;
      Result : Search_Result;
   begin
      while Pos <= A'Last loop
         if A(Pos) = Val then
            return Search_Result'(Found    => True,
                                  At_Index => Pos);
         end if;

         pragma Loop_Invariant
           (Pos in A'Range
              and then
            not Value_Found_In_Range (A, Val, A'First, Pos));
         pragma Loop_Variant (Increases => Pos);

         Pos := Pos + 1;
      end loop;

      return Search_Result'(Found => False);
   end Linear_Search;
end Search;
