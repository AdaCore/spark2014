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

package body At_Least_One_Lateral_Mode_Active is

   procedure comp
      (ROLL_Active : Boolean;
       HDG_Active : Boolean;
       NAV_Active : Boolean;
       LAPPR_Active : Boolean;
       LGA_Active : Boolean)
   is
      use type Boolean;
      HDG_Active_out1 : Boolean;
      LAPPR_Active_out1 : Boolean;
      LGA_Active_out1 : Boolean;
      NAV_Active_out1 : Boolean;
      ROLL_Active_out1 : Boolean;
      OR_out1 : Boolean;
   begin
      --  Block Mode_Logic_Props/Requirements/At_Least_One_Lateral_Mode_Active/HDG_Active
      HDG_Active_out1 := HDG_Active;
      --  End Block Mode_Logic_Props/Requirements/At_Least_One_Lateral_Mode_Active/HDG_Active

      --  Block Mode_Logic_Props/Requirements/At_Least_One_Lateral_Mode_Active/LAPPR_Active
      LAPPR_Active_out1 := LAPPR_Active;
      --  End Block Mode_Logic_Props/Requirements/At_Least_One_Lateral_Mode_Active/LAPPR_Active

      --  Block Mode_Logic_Props/Requirements/At_Least_One_Lateral_Mode_Active/LGA_Active
      LGA_Active_out1 := LGA_Active;
      --  End Block Mode_Logic_Props/Requirements/At_Least_One_Lateral_Mode_Active/LGA_Active

      --  Block Mode_Logic_Props/Requirements/At_Least_One_Lateral_Mode_Active/NAV_Active
      NAV_Active_out1 := NAV_Active;
      --  End Block Mode_Logic_Props/Requirements/At_Least_One_Lateral_Mode_Active/NAV_Active

      --  Block Mode_Logic_Props/Requirements/At_Least_One_Lateral_Mode_Active/ROLL_Active
      ROLL_Active_out1 := ROLL_Active;
      --  End Block Mode_Logic_Props/Requirements/At_Least_One_Lateral_Mode_Active/ROLL_Active

      --  Block Mode_Logic_Props/Requirements/At_Least_One_Lateral_Mode_Active/OR
      OR_out1 := ((((ROLL_Active_out1)
         or else (HDG_Active_out1))
            or else (NAV_Active_out1))
               or else (LAPPR_Active_out1))
                  or else (LGA_Active_out1);
      --  End Block Mode_Logic_Props/Requirements/At_Least_One_Lateral_Mode_Active/OR

      --  Block Mode_Logic_Props/Requirements/At_Least_One_Lateral_Mode_Active/My_Assertion
      pragma Assert (OR_out1, "Violation of assertion at block Mode_Logic_Props/Requirements/At_Least_One_Lateral_Mode_Active/My_Assertion");
      --  End Block Mode_Logic_Props/Requirements/At_Least_One_Lateral_Mode_Active/My_Assertion
   end comp;
end At_Least_One_Lateral_Mode_Active;
--  @EOF
