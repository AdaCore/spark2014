package Tick_Old_Implies_Input is
   G : Integer;

   procedure P1
     with Global => (Output => G),
          Post   => G = G'Old + 1;

   procedure P2 (X : out Integer)
     with Post => X = X'Old + 1;

   procedure P3
     with Post   => G = G'Old + 1;
end Tick_Old_Implies_Input;
