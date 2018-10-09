with P;

procedure Call1 (X : out P.T1) is
begin
   P.Proc1 (X); --  here discriminant is fixed, so only the X.C component is written
   P.Proc1 (X); --  and then the X.C value is over-written, so the first call was ineffective
end;
