with Q;
procedure P (X : Integer) with Ghost is
begin
   Q.Bar (X); -- shouldn't raise a check
end P;
