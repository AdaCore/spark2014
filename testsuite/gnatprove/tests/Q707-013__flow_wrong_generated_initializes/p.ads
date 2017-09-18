with Q; use Q; pragma Elaborate_All (Q);
package P
  with
  Elaborate_Body,
  Abstract_State => State,
  Initializes => (State => Ext)

is
private
   package Nested is
      Var : constant Natural := Ext with Part_Of => State;
   end;
end;
