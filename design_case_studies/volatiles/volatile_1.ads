-- This is a simple case of a volatile input abstract state named V_S
-- V_S may only be mentioned within the Global_Aspect or Dependency_Relation
-- of a procedure declared in the package specification.
-- Even in a simple case like this it is possible to place a postcondition
-- on the procedure Read as the type of the Value returned has to be known.
package Volatile_1
with
  Abstract_State => (Volatile => (V_S => Input))
is
   type T is private;

   function Is_Valid (V : T) return Boolean;

   procedure Read (Value : out T)
   with
     Global => (Input => V_S),
     Post   => Is_Valid (Value);

private
   type T is new Integer;

end Volatile_1;
