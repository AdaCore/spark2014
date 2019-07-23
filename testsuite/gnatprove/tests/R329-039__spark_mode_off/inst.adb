with Gen;

procedure Inst with SPARK_Mode is
   package G is new Gen (3);
begin
   pragma Assert (G.Get = 4);
end Inst;
