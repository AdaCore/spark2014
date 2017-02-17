package  P is
   type Type_Range is range 1 .. 10;
   function Bar_05 (A : in Integer;
                    B : in Type_Range)
                   return Boolean;
end P;
