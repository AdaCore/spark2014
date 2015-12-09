with Gen;
with Gen2;

procedure Main (X : Boolean) is
   Var : Integer := 10;

   package Inst is new Gen (X);
   package Inst2 is new Gen (True);
   package Inst3 is new Gen2 (Var);
begin
   pragma Assert (X = Inst.Get_Bounded);
   pragma Assert (Inst2.Get_Bounded);

   Inst3.Set (10);
   pragma Assert (Var = 10);
   pragma Assert (Inst3.Get = Var);
end Main;
