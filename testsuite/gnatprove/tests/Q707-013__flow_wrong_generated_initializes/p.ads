with Q;
package P
  with
  Elaborate_Body,
  Abstract_State => State,
  Initializes => (State => Q.Ext)

is
private
   package Nested is
      Var : constant Natural := Q.Ext with Part_Of => State;
   end;
end;
