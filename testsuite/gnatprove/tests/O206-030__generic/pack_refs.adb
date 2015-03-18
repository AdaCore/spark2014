package body Pack_Refs is
   function Func (Formal : Integer := Refs.External) return Integer is
   begin
      return Formal + Refs.External;
   end Func;
end Pack_Refs;
