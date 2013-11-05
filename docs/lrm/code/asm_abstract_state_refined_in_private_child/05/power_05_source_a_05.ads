--# inherit Power_05;
private package Power_05.Source_A_05
--# own State;
--# initializes State;
is
   procedure Read (Level : out Integer);
   --# global State;
   --# derives Level from State;
end Power_05.Source_A_05;
