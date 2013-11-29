-- In SPARK the parameter mode should be in out meaning that the
-- entire array is initialized before the call to the subprogram.
procedure Param_1_Legal (X : in out String)
is
begin
   if X'Length > 0 and X'First = 1 then
      X (1) := '?';
   end if;
end Param_1_Legal;
