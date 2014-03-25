----------------------------------------------------------------------------
--  Fun and games with interval propagation
--  interesting combinations.
------------------------------------------------------------------------------

package Interval_Reasoning
is
   pragma Elaborate_Body (Interval_Reasoning);

   type Large_Range is range -2**63 .. 2**63-1;
end Interval_Reasoning;
