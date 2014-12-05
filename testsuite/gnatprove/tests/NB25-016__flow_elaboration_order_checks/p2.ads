with P1;

package P2
  with Abstract_State => State,
       Initializes    => (State => P1.State)
is
   procedure P;
end P2;
