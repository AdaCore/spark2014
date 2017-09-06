package body Volatile_Placement
  with SPARK_Mode
is
   function Reg2 (R : Regnum) return Integer is
   begin
      return Integer (Regs (R));
   end Reg2;

end Volatile_Placement;
