procedure M (X, Z : Integer; Y : out Integer) with
  Depends => (Y => X,
              null => Z),
  Post => Y = X
  --  Contract is correct; need to ensure that the
  --  initialized value of C (i.e. Z) does *not*
  --  propagate into final dependency relation.
is
   type T (D : Integer) is record
      C : Integer := D;
   end record;

   A : T (D => Z);
begin
   A.C := X;
   Y := A.C;
end;
