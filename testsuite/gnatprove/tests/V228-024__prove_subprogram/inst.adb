with Gen;
procedure Inst is
   package G is new Gen;
   procedure I is new G.Incr;
begin
   null;
end Inst;
