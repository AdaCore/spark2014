procedure Renam6 (S : in out String) is
   X : Positive := S'First;

   generic
      Int_Obj : in out Character;
   procedure G with Global => null;

   procedure G is null;

   procedure I is new G (S (X));
begin
   S := S;
end;
