with Gen_Func;
with Gen_Func_Pragmas;
with Gen_Pack;
with Gen_Pack_Pragmas;
with Gen_Pack_Gen;
with Gen_Pack_Gen_Pragmas;
with Pack_Gen;
with Pack_Gen_Pragmas;

procedure Main is
   Local      : Integer := 0;
   Pack_Local : Integer := 0;

   --  Generic function (aspects)

   function Func_Inst_1 is new Gen_Func (Local);

   --  Generic function (pragmas)

   function Func_Inst_2 is new Gen_Func_Pragmas (Local);

   --  Generic package, normal function (aspects)

   package Pack_Inst_1 is new Gen_Pack (Pack_Local);

   --  Generic package, normal function (pragmas)

   package Pack_Inst_2 is new Gen_Pack_Pragmas (Pack_Local);

   --  Generic package, generic function (aspects)

   package Pack_Inst_3 is new Gen_Pack_Gen (Pack_Local);
   function Func_Inst_3 is new Pack_Inst_3.Func (Local);

   --  Generic package, generic function (pragmas)

   package Pack_Inst_4 is new Gen_Pack_Gen_Pragmas (Pack_Local);
   function Func_Inst_4 is new Pack_Inst_4.Func (Local);

   --  Normal package, generic function (aspects)

   function Func_Inst_6 is new Pack_Gen.Func (Local);

   --  Normal package, generic function (pragmas)

   function Func_Inst_7 is new Pack_Gen_Pragmas.Func (Local);

begin
   null;
end Main;
