package Volatile_Placement
  with SPARK_Mode
is
   type Regval is new Integer with Volatile;
   type Regnum is range 1 .. 32;
   type Registers is array (Regnum) of Regval;
   Regs : Registers with Async_Writers, Async_Readers;

   function Reg (R : Regnum) return Integer is (Integer (Regs (R)))
     with Volatile_Function;

   function Reg2 (R : Regnum) return Integer
     with Volatile_Function;

end Volatile_Placement;
