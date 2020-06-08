procedure Q (X : Integer; Y : out Integer) with
  Post => Y = X,
  Depends => (Y => X)
is
   type T (D : Integer) is record
      S : String (1 .. D);
   end record;

   A : T (D => X);
begin
   Y := A.S'Last;
end;
