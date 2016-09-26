package Outer2 is
   procedure P (Arg : out Integer) with Global => null;
   --  P531-027 regression: global contract should not be needed here
end Outer2;
