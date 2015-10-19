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

package At_Least_One_Lateral_Mode_Active is

   procedure comp
      (ROLL_Active : Boolean;
       HDG_Active : Boolean;
       NAV_Active : Boolean;
       LAPPR_Active : Boolean;
       LGA_Active : Boolean);

end At_Least_One_Lateral_Mode_Active;
--  @EOF
