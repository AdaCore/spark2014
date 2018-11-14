with P;

procedure Call (X : out P.T) is
begin
   P.Proc (X); --  we could argue that first call writes the discriminant of X
   P.Proc (X); --  which is then read by the second call, see call1.adb
end;
