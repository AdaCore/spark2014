with P;
with Tasks1;

procedure Main with Priority => 5 is  --  @CEILING_PRIORITY_PROTOCOL:FAIL

begin
   P.X.C1.Proc1;
   P.X.C2.Proc2;
   P.X.C3.Proc3;
   P.X.C4.Proc1;
end;
