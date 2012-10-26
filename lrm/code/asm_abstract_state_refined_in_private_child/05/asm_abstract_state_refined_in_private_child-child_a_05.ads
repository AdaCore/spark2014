--# inherit Power;
private package Power.Source_A
--# own State;
is
   procedure Read (Level : out Integer);
   --# global State;
   --# derives Level from State;
end Power.Source_A;
