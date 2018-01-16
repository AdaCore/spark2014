with P;

procedure Flip (Dummy : Integer) with Global => (In_Out => P.Solid_State);
--  We are adding a Dummy parameter as otherwise Flip will be wrongly considered
--  as a main subprogram of a partition. This is a known limitation documented
--  in the SPARK user guide (5.9.6).
