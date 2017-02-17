package body P is

   function Bar_05 (A : in Integer;
                    B : in Type_Range)
                   return Boolean
   is
   begin
      return Integer'Pos (A) > B;
   end Bar_05;
end P;
