function R (X, Y : Integer) return Boolean
  with Depends => (R'Result => (X, Y)),
       Post    => R'Result = (X = Y)
is
   type R (D : Integer) is null record;
   subtype S is R (Y);
begin
   return R'(D => X) in S;
end;
