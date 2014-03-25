------------------------------------------------------------------------------
--  These are test VCs which exercise private types.
------------------------------------------------------------------------------

with Complex, Stack;
use  Complex, Stack;


package Private_A
is
   pragma Elaborate_Body (Private_A);
end Private_A;
