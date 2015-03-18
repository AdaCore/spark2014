with Pack_Refs;

procedure Main_Refs is
   package  Pack_Inst is new Pack_Refs (1);
   function Func_Inst is new Pack_Inst.Func (2);

begin
   null;
end Main_Refs;
