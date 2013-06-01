package body Search is
   
   function Linear_Search 
     (A        : Arr; 
      Val      : Element; 
      At_Index : out Index) return Boolean 
   is
      Pos : Index := A'First;
   begin
      while Pos < A'Last loop
         if A(Pos) = Val then
            At_Index := Pos;
            return True;
         end if;

         Pos := Pos + 1;
      end loop;

      return False;
   end Linear_Search;
   
end Search;
