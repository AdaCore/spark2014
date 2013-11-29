-- The following example is acceptable in Ada
-- but will raise a flow anomaly in SPARK stating that
-- X may not be initialized because an out parameter indicates
-- that the entire String is initialized.
procedure Param_1_Illegal (X : out String)
is
begin
   if X'Length > 0 and X'First = 1 then
      X (1) := '?';
   end if;
end Param_1_Illegal;
