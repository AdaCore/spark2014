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

package Flight_Modes is

   procedure initStates;

   procedure initOutputs
      (Modes_On : out Boolean;
       FD_On : out Boolean;
       Independent_Mode : out Boolean;
       Active_Side : out Boolean;
       ROLL_Selected : out Boolean;
       ROLL_Active : out Boolean;
       HDG_Selected : out Boolean;
       HDG_Active : out Boolean;
       NAV_Selected : out Boolean;
       NAV_Active : out Boolean;
       LAPPR_Selected : out Boolean;
       LAPPR_Active : out Boolean;
       LGA_Selected : out Boolean;
       LGA_Active : out Boolean;
       PITCH_Selected : out Boolean;
       PITCH_Active : out Boolean;
       VS_Selected : out Boolean;
       VS_Active : out Boolean;
       FLC_Selected : out Boolean;
       FLC_Active : out Boolean;
       ALT_Selected : out Boolean;
       ALT_Active : out Boolean;
       ALTSEL_Selected : out Boolean;
       ALTSEL_Active : out Boolean;
       ALTSEL_Track : out Boolean;
       VAPPR_Selected : out Boolean;
       VAPPR_Active : out Boolean;
       VGA_Selected : out Boolean;
       VGA_Active : out Boolean);

   procedure comp
      (Pilot_Flying_Side : Boolean;
       Is_AP_Engaged : Boolean;
       Overspeed : Boolean;
       Is_Offside_FD_On : Boolean;
       Is_Offside_VAPPR_Active : Boolean;
       Is_Offside_VGA_Active : Boolean;
       Pilot_Flying_Transfer : Boolean;
       When_AP_Engaged : Boolean;
       SYNC_Switch_Pressed : Boolean;
       FD_Switch_Pressed : Boolean;
       HDG_Switch_Pressed : Boolean;
       NAV_Switch_Pressed : Boolean;
       APPR_Switch_Pressed : Boolean;
       GA_Switch_Pressed : Boolean;
       VS_Switch_Pressed : Boolean;
       FLC_Switch_Pressed : Boolean;
       ALT_Switch_Pressed : Boolean;
       VS_Pitch_Wheel_Rotated : Boolean;
       ALTSEL_Target_Changed : Boolean;
       NAV_Capture_Condition_Met : Boolean;
       LAPPR_Capture_Condition_Met : Boolean;
       ALTSEL_Capture_Condition_Met : Boolean;
       ALTSEL_Track_Condition_Met : Boolean;
       VAPPR_Capture_Condition_Met : Boolean;
       Selected_NAV_Source_Changed : Boolean;
       Selected_NAV_Frequency_Changed : Boolean;
       Modes_On : out Boolean;
       FD_On : out Boolean;
       Independent_Mode : out Boolean;
       Active_Side : out Boolean;
       ROLL_Selected : out Boolean;
       ROLL_Active : out Boolean;
       HDG_Selected : out Boolean;
       HDG_Active : out Boolean;
       NAV_Selected : out Boolean;
       NAV_Active : out Boolean;
       LAPPR_Selected : out Boolean;
       LAPPR_Active : out Boolean;
       LGA_Selected : out Boolean;
       LGA_Active : out Boolean;
       PITCH_Selected : out Boolean;
       PITCH_Active : out Boolean;
       VS_Selected : out Boolean;
       VS_Active : out Boolean;
       FLC_Selected : out Boolean;
       FLC_Active : out Boolean;
       ALT_Selected : out Boolean;
       ALT_Active : out Boolean;
       ALTSEL_Selected : out Boolean;
       ALTSEL_Active : out Boolean;
       ALTSEL_Track : out Boolean;
       VAPPR_Selected : out Boolean;
       VAPPR_Active : out Boolean;
       VGA_Selected : out Boolean;
       VGA_Active : out Boolean)
       with Post =>
         --  At least one lateral mode active
         ROLL_Active or HDG_Active or NAV_Active or LAPPR_Active or
         LGA_Active;

end Flight_Modes;
--  @EOF
