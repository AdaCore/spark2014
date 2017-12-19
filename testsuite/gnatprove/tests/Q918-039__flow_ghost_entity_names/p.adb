with Q;
procedure P (X : Integer) with Ghost is
begin
   Q.Foo (X); -- should raise a check
   Q.Bar (X); -- shouldn't raise a check
end P;
