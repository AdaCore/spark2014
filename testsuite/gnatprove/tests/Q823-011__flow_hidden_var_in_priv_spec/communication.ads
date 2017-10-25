with Other; use Other;
package Communication
  with Abstract_State => State,
  Initializes => (State => V_Ext)
is
   procedure Dummy;
private
   Max : constant Natural := V_Ext; -- needs Part_Of
end;
