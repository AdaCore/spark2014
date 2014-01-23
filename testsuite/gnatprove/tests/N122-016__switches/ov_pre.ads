package Ov_Pre is

   procedure P (X : Integer)
      with Pre => X * X < Integer'Last;
end Ov_Pre;
