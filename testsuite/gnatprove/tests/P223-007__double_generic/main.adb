with Gen1;

procedure Main is
   X : Integer;
   package Inst1 is new Gen1 (X);
begin
   Inst1.Inst2.Set (0);
   pragma Assert (X = 0);
end;
