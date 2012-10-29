-- Use of child packages to encapsulate state
package Power_14
with
   Abstract_State => State;
is
   procedure Read_Power(Level : out Integer);
   with
      Global  => State,
      Depends => (Level => State);
end Power_14;
