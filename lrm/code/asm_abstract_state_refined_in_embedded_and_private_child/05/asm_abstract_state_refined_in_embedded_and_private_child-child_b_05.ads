--# inherit Power;
private package Power.Source_B
--# own State;
is
   procedure Read (Level : out Integer);
   --# global State;
   --# derives Level from State;
end Power.Source_B;
