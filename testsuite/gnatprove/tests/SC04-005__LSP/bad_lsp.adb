package body Bad_LSP  is
   procedure Pr (X : in out Root; Res : out Boolean) is
   begin
      Res := (X.F + X.G >= 100);
      X.F := 130;
   end Pr;
   procedure Pr (X : in out Child; Res : out Boolean) is
   begin
      Res := (X.F >= 100 or else X.G >= 100 or else X.F + X.G >= 100);
      X.G := 130;
   end Pr;
end Bad_LSP;
