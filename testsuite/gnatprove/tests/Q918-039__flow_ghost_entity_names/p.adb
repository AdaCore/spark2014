with Q;
procedure P (X : Integer) with Ghost is
begin
   Q.Foo (X);
end P;
