with Lemma;
procedure Inst is
   package My is new
     Lemma (Float, 2.0**63);
begin
   null;
end Inst;
