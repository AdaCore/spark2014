package body Callee is
   procedure Add(i1 : in out Integer; i2: Integer) is
   begin
      i1 := i1 + i2;
   end Add;
end Callee;
