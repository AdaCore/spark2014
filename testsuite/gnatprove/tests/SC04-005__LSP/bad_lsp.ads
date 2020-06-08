package Bad_LSP  is
   pragma Elaborate_Body;
   pragma Unevaluated_Use_Of_Old (Allow);
   type Root is tagged record
      F : Natural;
      G : Natural;
   end record;
   procedure Pr (X : in out Root; Res : out Boolean)
   with Pre'Class => X.F <= 100 and X.G <= 100,
     Post'Class => (if Res then Natural'(X.F + X.G)'Old >= 100); --@OVERFLOW_CHECK:FAIL
   type Child is new Root with record
      H : Natural;
   end record;
   overriding
   procedure Pr (X : in out Child; Res : out Boolean) with
     Pre'Class => True;
end Bad_LSP;
