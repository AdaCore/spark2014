with Refs;

generic
   Outer : Integer;

package Pack_Refs is
   generic
      Inner : Integer;

   function Func (Formal : Integer := Refs.External) return Integer
     with Pre  => Refs.External > 0,
          Post => Func'Result = Formal + Refs.External,
          Contract_Cases => (Formal < 0 => True,
                             Formal = 0 => Func'Result > 0,
                             Formal > 0 => Func'Result > Formal);
end Pack_Refs;
