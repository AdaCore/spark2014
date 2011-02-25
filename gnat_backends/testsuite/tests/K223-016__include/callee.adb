package body Callee is
   procedure Add(A : in out Integer; B : Integer) is
   begin
      A := A + B;
   end Add;
end Callee;
