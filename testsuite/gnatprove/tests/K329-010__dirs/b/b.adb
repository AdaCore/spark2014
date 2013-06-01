with A;

procedure B is
   X : A.T;
begin
   X := A.any;
   pragma Assert (X > 2);
end B;

