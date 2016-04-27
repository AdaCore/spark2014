--  This package does not require an Elaborate_Body since E is not declared
--  in the initialisation (but is changed) and B is a) not changed and b)
--  not declared.

package Init with
   Abstract_State => State,
   Initializes    => (State, C)
is

   B : Integer := 0;
   C : constant Integer := B;
   E : Integer;

   procedure Dummy;

end Init;
