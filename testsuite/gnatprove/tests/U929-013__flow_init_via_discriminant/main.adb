procedure Main (X : Integer; Y : out Integer) with
  Depends => (Y => X),
  Post => Y = X
  --  Contract is correct
is
   type T (D : Integer) is record
      C : Integer := D;
   end record;

   A : T (D => X);
begin
   Y := A.C;
end;
