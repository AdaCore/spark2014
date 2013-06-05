-- Use of child packages to encapsulate state
package Power_05
--# own State;
is
   procedure Read_Power(Level : out Integer);
   --# global State;
   --# derives Level from State;
end Power_05;
