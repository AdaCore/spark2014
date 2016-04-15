procedure Unmod (X : in out Integer)
is
   pragma Unmodified(X);
   pragma Unmodified(X);
begin
   null;
end;
