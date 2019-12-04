with Bad_LSP; use Bad_LSP;
procedure Test_LSP is
   R : Boolean;
   C : Child := (others => Natural'Last);
begin
   Bad_LSP.Pr (C, R);
end Test_LSP;
