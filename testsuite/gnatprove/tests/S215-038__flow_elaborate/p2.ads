--with P;
package P2
  with Abstract_State => State
--       Initializes    => (State => P.State)
--
--  When P.State is known by Entity_Id, then flow says that pragma Elaborate
--  (P) is needed; when it is known by Entity_Name, then it doesn't.
is
   procedure Dummy with Global => null; -- just to force package body
end P2;
