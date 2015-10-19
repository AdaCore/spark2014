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

package Event_Processing is

   procedure initStates;

   procedure comp
      (Is_Pilot_Flying_Side : Boolean;
       AP_Engaged : Boolean;
       SYNC_Switch : Boolean;
       FD_Switch : Boolean;
       HDG_Switch : Boolean;
       NAV_Switch : Boolean;
       APPR_Switch : Boolean;
       GA_Switch : Boolean;
       VS_Switch : Boolean;
       FLC_Switch : Boolean;
       ALT_Switch : Boolean;
       VS_Pitch_Wheel_Rotated : Boolean;
       ALTSEL_Target_Changed : Boolean;
       NAV_Capture_Cond_Met : Boolean;
       LAPPR_Capture_Cond_Met : Boolean;
       ALTSEL_Capture_Cond_Met : Boolean;
       ALTSEL_Track_Cond_Met : Boolean;
       VAPPR_Capture_Cond_Met : Boolean;
       When_Pilot_Fllying_Transfer_Seen : out Boolean;
       When_AP_Engaged_Seen : out Boolean;
       When_SYNC_Switch_Pressed_Seen : out Boolean;
       When_FD_Switch_Pressed_Seen : out Boolean;
       When_HDG_Switch_Pressed_Seen : out Boolean;
       When_NAV_Switch_Pressed_Seen : out Boolean;
       When_APPR_Switch_Pressed_Seen : out Boolean;
       When_GA_Switch_Pressed_Seen : out Boolean;
       When_VS_Switch_Pressed_Seen : out Boolean;
       When_FLC_Switch_Pressed_Seen : out Boolean;
       When_ALT_Switch_Pressed_Seen : out Boolean;
       When_VS_Pitch_Wheel_Rotated_Seen : out Boolean;
       When_ALTSEL_Target_Changed_Seen : out Boolean;
       If_NAV_Capture_Cond_Met_Seen : out Boolean;
       If_LAPPR_Capture_Cond_Met_Seen : out Boolean;
       If_ALTSEL_Capture_Cond_Met_Seen : out Boolean;
       If_ALTSEL_Track_Cond_Met_Seen : out Boolean;
       If_VAPPR_Capture_Cond_Met_Seen : out Boolean);

   procedure up;

end Event_Processing;
--  @EOF
