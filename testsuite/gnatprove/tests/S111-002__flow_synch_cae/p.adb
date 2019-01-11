package body P is
   procedure Swap (A, B : in out T) is
      Tmp : constant Integer := A.C;
   begin
      A.C := B.C;
      B.C := Tmp;
   end;

begin
   Swap (X, X);
   --  Actual parameter X is aliasing with itself
end P;
