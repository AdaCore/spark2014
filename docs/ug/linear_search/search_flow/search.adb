package body Search is
   
   function Linear_Search 
     (A   : Arr; 
      Val : Element) return Search_Result
   is
      Pos : Index := A'First;
      Res : Search_Result;
   begin
      while Pos < A'Last loop
         if A(Pos) = Val then
            Res.At_Index := Pos;
            Res.Found := True;
            return Res;
         end if;

         Pos := Pos + 1;
      end loop;

      Res.Found := False;
      return Res;
   end Linear_Search;
   
end Search;
