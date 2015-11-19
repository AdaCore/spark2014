package Res_Size is

   type Arr is array (Integer range <>) of Integer;

   function F (A : Arr) return Arr
      with Post => F'Result'Size = A'Size;

end Res_Size;
