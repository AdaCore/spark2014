with Q;
-- The Dummy parameter is to avoid a spurious message for procedure P that could
-- be wrongly considered as a main. This is a known limitation documented in
-- the SPARK UG 5.9.6.
procedure P (Dummy : Integer) is
begin
   null;
end P;
