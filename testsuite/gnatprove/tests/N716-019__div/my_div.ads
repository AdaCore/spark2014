package My_Div
is

   type My_Int is mod 2 ** 32;

   procedure P (X : in out My_Int)
      with Post => (X = X'Old / 64);

   procedure Q (X : in out My_Int);
end My_Div;
