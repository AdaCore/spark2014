-- This example is a bit more complex.  The procedure Input_Is_Rising has a
-- Boolean out parameter which is true if two successive inputs are increasing
-- in value.  It is false if they are the same or falling.  We do not know the
-- type of the external input values within the package specification.
package Volatile_2
with
  Abstract_State => (Volatile => (V_S => (Input))

is

   procedure Input_Is_Rising (Rising : out Boolean)
   with
     Global => (Input => V_S);

end Volatile_2;
