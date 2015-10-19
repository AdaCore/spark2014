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

package NAV_Active_When_Capture_Cond_Met is

   procedure initStates;

   procedure comp
      (Pilot_Flying_Side : Boolean;
       Selected_NAV_Source_Changed : Boolean;
       Selected_NAV_Frequency_Changed : Boolean;
       NAV_Capture_Cond_Met : Boolean;
       No_Higher_Event_Than_NAV_Capture_Cond_Met : Boolean;
       NAV_Active : Boolean;
       Modes_On : Boolean);

   procedure up (NAV_Selected : Boolean);

end NAV_Active_When_Capture_Cond_Met;
--  @EOF
