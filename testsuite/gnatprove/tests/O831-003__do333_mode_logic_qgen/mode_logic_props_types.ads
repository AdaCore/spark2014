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

package Mode_Logic_Props_types is

   subtype Boolean_Array_15_Range_1 is Integer range 0 .. 14;
   type Boolean_Array_15 is array (Boolean_Array_15_Range_1) of Boolean;
   type mode_logic_inputs is record
      Pilot_Flying_Side : Boolean;
      Is_AP_Engaged : Boolean;
      Overspeed : Boolean;
      Offside_FD_On : Boolean;
      Is_Offside_VAPPR_Active : Boolean;
      Is_Offside_VGA_Active : Boolean;
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
      Selected_Nav_Source_Changed : Boolean;
      Selected_Nav_Frequency_Changed : Boolean;
   end record;

   type mode_logic_outputs is record
      Modes_On : Boolean;
      FD_On : Boolean;
      Independent_Mode : Boolean;
      Active_Side : Boolean;
      ROLL_Selected : Boolean;
      ROLL_Active : Boolean;
      HDG_Selected : Boolean;
      HDG_Active : Boolean;
      NAV_Selected : Boolean;
      NAV_Active : Boolean;
      LAPPR_Selected : Boolean;
      LAPPR_Active : Boolean;
      LGA_Selected : Boolean;
      LGA_Active : Boolean;
      PITCH_Selected : Boolean;
      PITCH_Active : Boolean;
      VS_Selected : Boolean;
      VS_Active : Boolean;
      FLC_Selected : Boolean;
      FLC_Active : Boolean;
      ALT_Selected : Boolean;
      ALT_Active : Boolean;
      ALTSEL_Selected : Boolean;
      ALTSEL_Active : Boolean;
      ALTSEL_Track : Boolean;
      VAPPR_Selected : Boolean;
      VAPPR_Active : Boolean;
      VGA_Selected : Boolean;
      VGA_Active : Boolean;
   end record;

   type no_higher_event is record
      No_Higher_Event_Than_SYNC_Switch_Pressed : Boolean;
      No_Higher_Event_Than_GA_Switch_Pressed : Boolean;
      No_Higher_Event_Than_APPR_Switch_Pressed : Boolean;
      No_Higher_Event_Than_HDG_Switch_Pressed : Boolean;
      No_Higher_Event_Than_AP_Engaged : Boolean;
      No_Higher_Event_Than_ALTSEL_Target_Changed : Boolean;
      No_Higher_Event_Than_ALT_Switch_Pressed : Boolean;
      No_Higher_Event_Than_FLC_Switch_Pressed : Boolean;
      No_Higher_Event_Than_VS_Switch_Pressed : Boolean;
      No_Higher_Event_Than_FD_Switch_Pressed : Boolean;
      No_Higher_Event_Than_LAPPR_Capture_Cond_Met : Boolean;
      No_Higher_Event_Than_NAV_Capture_Cond_Met : Boolean;
      No_Higher_Event_Than_VAPPR_Capture_Cond_Met : Boolean;
      No_Higher_Event_Than_ALTSEL_Capture_Cond_Met : Boolean;
      No_Higher_Event_Than_ALTSEL_Track_Cond_Met : Boolean;
   end record;

   type Rising_Edge_State is record
      Unit_Delay_memory : Boolean;
      In1_out1 : Boolean;
   end record;

   type Changed_State is record
      Unit_Delay_memory : Boolean;
      In1_out1 : Boolean;
   end record;

end Mode_Logic_Props_types;
--  @EOF
