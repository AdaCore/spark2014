package body P is
begin
   CAE := Fun;
   --  SPARK RM 6.1.4(20): subprogram [Fun] with a global input/proof_in
   --  denoting a constant-after-elaboration [CAE] shall not be called during
   --  library unit elaboration.
end;
