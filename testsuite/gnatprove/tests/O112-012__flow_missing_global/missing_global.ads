package Missing_Global is
   G1, G2 : Integer := 0;

   procedure P1 (X : out Integer)
     with Global => G1;

   procedure P2 (X : out Integer);

   procedure P3 (X : out Integer)
     with Global => G1;
end Missing_Global;
