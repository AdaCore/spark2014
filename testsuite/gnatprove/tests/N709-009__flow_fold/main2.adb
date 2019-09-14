procedure Main2 (X : in out Boolean) with Global => null is

   function F return Boolean is (True) with Pre => X, Global => (Proof_In => X);

   procedure Test with Global => (Proof_In => X) is
   begin
      pragma Assert (F);
   end;
begin
   Test;
   X := not X;
end;
