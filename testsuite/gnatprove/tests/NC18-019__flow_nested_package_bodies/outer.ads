package Outer is
   procedure P (X : out Integer) with Global => null;
   --  P531-027 regression: the global contract should not be necessary

   procedure P2 (X : out Integer);

   procedure P3;

   procedure P4 (X : out Integer);
end Outer;
