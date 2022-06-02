package P with Initializes => X, Initial_Condition => X is
   X : Boolean := True;
   function Get return Boolean with Pure_Function, Global => X, Post => Get'Result = X;
   procedure Reset with Global => (Output => X), Post => not X;
end;
