--  Copyright (C) Your Company Name
--
--  @generated with QGen Code Generator 2.0.0w (20150420)
--  Command line arguments:
--    --clean models/case_studies/NASA-DO-333-Case-Studies/Mode_Logic_Case_Study_Files/Mode_Logic_Props.mdl
--    --output models/case_studies/NASA-DO-333-Case-Studies/Mode_Logic_Case_Study_Files/Mode_Logic_Props/hmc_ada
--    --language ada
--    --debug
--    --typing models/case_studies/NASA-DO-333-Case-Studies/Mode_Logic_Case_Study_Files/Mode_Logic_Props_types.txt

pragma Style_Checks ("M999");  --  ignore long lines

with Mode_Logic_Props_types; use Mode_Logic_Props_types;

package Rising_Edge is

   procedure initStates (State : in out Rising_Edge_State);

   procedure comp
      (In1 : Boolean;
       Out1 : out Boolean;
       State : in out Rising_Edge_State);

   procedure up (State : in out Rising_Edge_State);

end Rising_Edge;
--  @EOF
