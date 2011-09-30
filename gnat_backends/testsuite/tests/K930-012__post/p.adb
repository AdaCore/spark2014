package body P is
   procedure Swap (A : in out Arr; J, K : Index) is
      Tmp : Integer := A(J);
   begin
      A(J) := A(K);
      A(K) := Tmp;
   end Swap;
end P;
