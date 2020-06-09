with Other;
package Q.Priv.Pub with Abstract_State =>
  (Pubs_State with Part_Of => Q.State),
    Initializes => (Pubs_State => Other.V)
is
private
   C : constant Integer := Other.V with Part_Of => Pubs_State;
   --  Constant with variable input; it should be Part_Of a state
   --  declared in this package, which in turn should be Part_Of => Q.State.
   D : constant Integer := Other.W; -- with Part_Of => Pubs_State;
   --  Constant with constant input; this should *not* be Part_Of
   --  state declared in this package.
   procedure Dummy with Global => null;
end;
