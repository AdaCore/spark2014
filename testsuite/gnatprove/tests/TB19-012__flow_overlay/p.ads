package P is
   A : Integer := 0 with Alignment => 4;
   B : Integer with Address => A'Address, Alignment => 4, Import;
   function Zero return Boolean is (B = 0) with Global => A;
end;
