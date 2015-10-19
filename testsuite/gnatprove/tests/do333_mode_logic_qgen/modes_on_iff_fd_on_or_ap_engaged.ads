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

package Modes_On_Iff_FD_On_or_AP_Engaged is

   procedure initStates;

   procedure comp
      (Offside_FD_On : Boolean;
       Is_AP_Engaged : Boolean;
       FD_On : Boolean;
       Modes_On : Boolean);

   procedure up;

end Modes_On_Iff_FD_On_or_AP_Engaged;
--  @EOF
