package body Const is
   function Add_Everything return Integer
   is (A + B + C + D + E + F + G + H + I);
   --  The globals of Add_Everything should only mention A, B, C, D
   --  and E. On the other hand F, G, H and I are not constants with
   --  variable inputs so they should NOT be mentioned.
end Const;
