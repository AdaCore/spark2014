package body Root_Pkg is
   function Op_Wrapper (Y : Root'Class) return Boolean is
   begin
      return Op (Y);
   end;
end;
