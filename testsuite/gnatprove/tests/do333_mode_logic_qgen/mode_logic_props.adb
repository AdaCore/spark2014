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

with Event_Processing; use Event_Processing;
with Flight_Modes; use Flight_Modes;
with Requirements; use Requirements;

package body Mode_Logic_Props is
   Flight_Modes_Modes_On : Boolean;
   Flight_Modes_FD_On : Boolean;
   Flight_Modes_Independent_Mode : Boolean;
   Flight_Modes_Active_Side : Boolean;
   Flight_Modes_ROLL_Selected : Boolean;
   Flight_Modes_ROLL_Active : Boolean;
   Flight_Modes_HDG_Selected : Boolean;
   Flight_Modes_HDG_Active : Boolean;
   Flight_Modes_NAV_Selected : Boolean;
   Flight_Modes_NAV_Active : Boolean;
   Flight_Modes_LAPPR_Selected : Boolean;
   Flight_Modes_LAPPR_Active : Boolean;
   Flight_Modes_LGA_Selected : Boolean;
   Flight_Modes_LGA_Active : Boolean;
   Flight_Modes_PITCH_Selected : Boolean;
   Flight_Modes_PITCH_Active : Boolean;
   Flight_Modes_VS_Selected : Boolean;
   Flight_Modes_VS_Active : Boolean;
   Flight_Modes_FLC_Selected : Boolean;
   Flight_Modes_FLC_Active : Boolean;
   Flight_Modes_ALT_Selected : Boolean;
   Flight_Modes_ALT_Active : Boolean;
   Flight_Modes_ALTSEL_Selected : Boolean;
   Flight_Modes_ALTSEL_Active : Boolean;
   Flight_Modes_ALTSEL_Track : Boolean;
   Flight_Modes_VAPPR_Selected : Boolean;
   Flight_Modes_VAPPR_Active : Boolean;
   Flight_Modes_VGA_Selected : Boolean;
   Flight_Modes_VGA_Active : Boolean;

   procedure initStates;

   procedure initOutputs;

   procedure init is
   begin
      Mode_Logic_Props.initStates;
      Mode_Logic_Props.initOutputs;
   end init;

   procedure comp (Inputs : mode_logic_inputs) is
      use type Boolean;
      use type mode_logic_inputs;
      use type mode_logic_outputs;
      Inputs_out1 : mode_logic_inputs;
      Pilot_Flying_Side : Boolean;
      Is_AP_Engaged : Boolean;
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
      Overspeed : Boolean;
      ALTSEL_Track_Cond_Met : Boolean;
      VAPPR_Capture_Cond_Met : Boolean;
      Selected_Nav_Source_Changed : Boolean;
      Selected_Nav_Frequency_Changed : Boolean;
      Offside_FD_On : Boolean;
      Is_Offside_VAPPR_Active : Boolean;
      Is_Offside_VGA_Active : Boolean;
      SYNC_Switch : Boolean;
      FD_Switch : Boolean;
      HDG_Switch : Boolean;
      NAV_Switch : Boolean;
      Event_Processing_When_Pilot_Fllying_Transfer_Seen : Boolean;
      Event_Processing_When_AP_Engaged_Seen : Boolean;
      Event_Processing_When_SYNC_Switch_Pressed_Seen : Boolean;
      Event_Processing_When_FD_Switch_Pressed_Seen : Boolean;
      Event_Processing_When_HDG_Switch_Pressed_Seen : Boolean;
      Event_Processing_When_NAV_Switch_Pressed_Seen : Boolean;
      Event_Processing_When_APPR_Switch_Pressed_Seen : Boolean;
      Event_Processing_When_GA_Switch_Pressed_Seen : Boolean;
      Event_Processing_When_VS_Switch_Pressed_Seen : Boolean;
      Event_Processing_When_FLC_Switch_Pressed_Seen : Boolean;
      Event_Processing_When_ALT_Switch_Pressed_Seen : Boolean;
      Event_Processing_When_VS_Pitch_Wheel_Rotated_Seen : Boolean;
      Event_Processing_When_ALTSEL_Target_Changed_Seen : Boolean;
      Event_Processing_If_NAV_Capture_Cond_Met_Seen : Boolean;
      Event_Processing_If_LAPPR_Capture_Cond_Met_Seen : Boolean;
      Event_Processing_If_ALTSEL_Capture_Cond_Met_Seen : Boolean;
      Event_Processing_If_ALTSEL_Track_Cond_Met_Seen : Boolean;
      Event_Processing_If_VAPPR_Capture_Cond_Met_Seen : Boolean;
      Bus_Creator_out1 : mode_logic_outputs;
   begin
      --  Block Mode_Logic_Props/Inputs
      Inputs_out1 := Inputs;
      --  End Block Mode_Logic_Props/Inputs

      --  Block Mode_Logic_Props/Bus\nSelector
      Pilot_Flying_Side := Inputs_out1.Pilot_Flying_Side;
      --  End Block Mode_Logic_Props/Bus\nSelector

      --  Block Mode_Logic_Props/Bus\nSelector1
      Is_AP_Engaged := Inputs_out1.Is_AP_Engaged;
      --  End Block Mode_Logic_Props/Bus\nSelector1

      --  Block Mode_Logic_Props/Bus\nSelector10
      APPR_Switch := Inputs_out1.APPR_Switch;
      --  End Block Mode_Logic_Props/Bus\nSelector10

      --  Block Mode_Logic_Props/Bus\nSelector11
      GA_Switch := Inputs_out1.GA_Switch;
      --  End Block Mode_Logic_Props/Bus\nSelector11

      --  Block Mode_Logic_Props/Bus\nSelector12
      VS_Switch := Inputs_out1.VS_Switch;
      --  End Block Mode_Logic_Props/Bus\nSelector12

      --  Block Mode_Logic_Props/Bus\nSelector13
      FLC_Switch := Inputs_out1.FLC_Switch;
      --  End Block Mode_Logic_Props/Bus\nSelector13

      --  Block Mode_Logic_Props/Bus\nSelector14
      ALT_Switch := Inputs_out1.ALT_Switch;
      --  End Block Mode_Logic_Props/Bus\nSelector14

      --  Block Mode_Logic_Props/Bus\nSelector15
      VS_Pitch_Wheel_Rotated := Inputs_out1.VS_Pitch_Wheel_Rotated;
      --  End Block Mode_Logic_Props/Bus\nSelector15

      --  Block Mode_Logic_Props/Bus\nSelector16
      ALTSEL_Target_Changed := Inputs_out1.ALTSEL_Target_Changed;
      --  End Block Mode_Logic_Props/Bus\nSelector16

      --  Block Mode_Logic_Props/Bus\nSelector17
      NAV_Capture_Cond_Met := Inputs_out1.NAV_Capture_Cond_Met;
      --  End Block Mode_Logic_Props/Bus\nSelector17

      --  Block Mode_Logic_Props/Bus\nSelector18
      LAPPR_Capture_Cond_Met := Inputs_out1.LAPPR_Capture_Cond_Met;
      --  End Block Mode_Logic_Props/Bus\nSelector18

      --  Block Mode_Logic_Props/Bus\nSelector19
      ALTSEL_Capture_Cond_Met := Inputs_out1.ALTSEL_Capture_Cond_Met;
      --  End Block Mode_Logic_Props/Bus\nSelector19

      --  Block Mode_Logic_Props/Bus\nSelector2
      Overspeed := Inputs_out1.Overspeed;
      --  End Block Mode_Logic_Props/Bus\nSelector2

      --  Block Mode_Logic_Props/Bus\nSelector20
      ALTSEL_Track_Cond_Met := Inputs_out1.ALTSEL_Track_Cond_Met;
      --  End Block Mode_Logic_Props/Bus\nSelector20

      --  Block Mode_Logic_Props/Bus\nSelector21
      VAPPR_Capture_Cond_Met := Inputs_out1.VAPPR_Capture_Cond_Met;
      --  End Block Mode_Logic_Props/Bus\nSelector21

      --  Block Mode_Logic_Props/Bus\nSelector22
      Selected_Nav_Source_Changed := Inputs_out1.Selected_Nav_Source_Changed;
      --  End Block Mode_Logic_Props/Bus\nSelector22

      --  Block Mode_Logic_Props/Bus\nSelector26
      Selected_Nav_Frequency_Changed := Inputs_out1.Selected_Nav_Frequency_Changed;
      --  End Block Mode_Logic_Props/Bus\nSelector26

      --  Block Mode_Logic_Props/Bus\nSelector3
      Offside_FD_On := Inputs_out1.Offside_FD_On;
      --  End Block Mode_Logic_Props/Bus\nSelector3

      --  Block Mode_Logic_Props/Bus\nSelector4
      Is_Offside_VAPPR_Active := Inputs_out1.Is_Offside_VAPPR_Active;
      --  End Block Mode_Logic_Props/Bus\nSelector4

      --  Block Mode_Logic_Props/Bus\nSelector5
      Is_Offside_VGA_Active := Inputs_out1.Is_Offside_VGA_Active;
      --  End Block Mode_Logic_Props/Bus\nSelector5

      --  Block Mode_Logic_Props/Bus\nSelector6
      SYNC_Switch := Inputs_out1.SYNC_Switch;
      --  End Block Mode_Logic_Props/Bus\nSelector6

      --  Block Mode_Logic_Props/Bus\nSelector7
      FD_Switch := Inputs_out1.FD_Switch;
      --  End Block Mode_Logic_Props/Bus\nSelector7

      --  Block Mode_Logic_Props/Bus\nSelector8
      HDG_Switch := Inputs_out1.HDG_Switch;
      --  End Block Mode_Logic_Props/Bus\nSelector8

      --  Block Mode_Logic_Props/Bus\nSelector9
      NAV_Switch := Inputs_out1.NAV_Switch;
      --  End Block Mode_Logic_Props/Bus\nSelector9

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing
      Event_Processing.comp (Pilot_Flying_Side, Is_AP_Engaged, SYNC_Switch, FD_Switch, HDG_Switch, NAV_Switch, APPR_Switch, GA_Switch, VS_Switch, FLC_Switch, ALT_Switch, VS_Pitch_Wheel_Rotated, ALTSEL_Target_Changed, NAV_Capture_Cond_Met, LAPPR_Capture_Cond_Met, ALTSEL_Capture_Cond_Met, ALTSEL_Track_Cond_Met, VAPPR_Capture_Cond_Met, Event_Processing_When_Pilot_Fllying_Transfer_Seen, Event_Processing_When_AP_Engaged_Seen, Event_Processing_When_SYNC_Switch_Pressed_Seen, Event_Processing_When_FD_Switch_Pressed_Seen, Event_Processing_When_HDG_Switch_Pressed_Seen, Event_Processing_When_NAV_Switch_Pressed_Seen, Event_Processing_When_APPR_Switch_Pressed_Seen, Event_Processing_When_GA_Switch_Pressed_Seen, Event_Processing_When_VS_Switch_Pressed_Seen, Event_Processing_When_FLC_Switch_Pressed_Seen, Event_Processing_When_ALT_Switch_Pressed_Seen, Event_Processing_When_VS_Pitch_Wheel_Rotated_Seen, Event_Processing_When_ALTSEL_Target_Changed_Seen, Event_Processing_If_NAV_Capture_Cond_Met_Seen, Event_Processing_If_LAPPR_Capture_Cond_Met_Seen, Event_Processing_If_ALTSEL_Capture_Cond_Met_Seen, Event_Processing_If_ALTSEL_Track_Cond_Met_Seen, Event_Processing_If_VAPPR_Capture_Cond_Met_Seen);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing

      --  Block Mode_Logic_Props/Mode_Logic/Flight_Modes
      Flight_Modes.comp (Pilot_Flying_Side, Is_AP_Engaged, Overspeed, Offside_FD_On, Is_Offside_VAPPR_Active, Is_Offside_VGA_Active, Event_Processing_When_Pilot_Fllying_Transfer_Seen, Event_Processing_When_AP_Engaged_Seen, Event_Processing_When_SYNC_Switch_Pressed_Seen, Event_Processing_When_FD_Switch_Pressed_Seen, Event_Processing_When_HDG_Switch_Pressed_Seen, Event_Processing_When_NAV_Switch_Pressed_Seen, Event_Processing_When_APPR_Switch_Pressed_Seen, Event_Processing_When_GA_Switch_Pressed_Seen, Event_Processing_When_VS_Switch_Pressed_Seen, Event_Processing_When_FLC_Switch_Pressed_Seen, Event_Processing_When_ALT_Switch_Pressed_Seen, Event_Processing_When_VS_Pitch_Wheel_Rotated_Seen, Event_Processing_When_ALTSEL_Target_Changed_Seen, Event_Processing_If_NAV_Capture_Cond_Met_Seen, Event_Processing_If_LAPPR_Capture_Cond_Met_Seen, Event_Processing_If_ALTSEL_Capture_Cond_Met_Seen, Event_Processing_If_ALTSEL_Track_Cond_Met_Seen, Event_Processing_If_VAPPR_Capture_Cond_Met_Seen, Selected_Nav_Source_Changed, Selected_Nav_Frequency_Changed, Flight_Modes_Modes_On, Flight_Modes_FD_On, Flight_Modes_Independent_Mode, Flight_Modes_Active_Side, Flight_Modes_ROLL_Selected, Flight_Modes_ROLL_Active, Flight_Modes_HDG_Selected, Flight_Modes_HDG_Active, Flight_Modes_NAV_Selected, Flight_Modes_NAV_Active, Flight_Modes_LAPPR_Selected, Flight_Modes_LAPPR_Active, Flight_Modes_LGA_Selected, Flight_Modes_LGA_Active, Flight_Modes_PITCH_Selected, Flight_Modes_PITCH_Active, Flight_Modes_VS_Selected, Flight_Modes_VS_Active, Flight_Modes_FLC_Selected, Flight_Modes_FLC_Active, Flight_Modes_ALT_Selected, Flight_Modes_ALT_Active, Flight_Modes_ALTSEL_Selected, Flight_Modes_ALTSEL_Active, Flight_Modes_ALTSEL_Track, Flight_Modes_VAPPR_Selected, Flight_Modes_VAPPR_Active, Flight_Modes_VGA_Selected, Flight_Modes_VGA_Active);
      --  End Block Mode_Logic_Props/Mode_Logic/Flight_Modes

      --  Block Mode_Logic_Props/Bus\nCreator
      Bus_Creator_out1.Modes_On := Flight_Modes_Modes_On;
      Bus_Creator_out1.FD_On := Flight_Modes_FD_On;
      Bus_Creator_out1.Independent_Mode := Flight_Modes_Independent_Mode;
      Bus_Creator_out1.Active_Side := Flight_Modes_Active_Side;
      Bus_Creator_out1.ROLL_Selected := Flight_Modes_ROLL_Selected;
      Bus_Creator_out1.ROLL_Active := Flight_Modes_ROLL_Active;
      Bus_Creator_out1.HDG_Selected := Flight_Modes_HDG_Selected;
      Bus_Creator_out1.HDG_Active := Flight_Modes_HDG_Active;
      Bus_Creator_out1.NAV_Selected := Flight_Modes_NAV_Selected;
      Bus_Creator_out1.NAV_Active := Flight_Modes_NAV_Active;
      Bus_Creator_out1.LAPPR_Selected := Flight_Modes_LAPPR_Selected;
      Bus_Creator_out1.LAPPR_Active := Flight_Modes_LAPPR_Active;
      Bus_Creator_out1.LGA_Selected := Flight_Modes_LGA_Selected;
      Bus_Creator_out1.LGA_Active := Flight_Modes_LGA_Active;
      Bus_Creator_out1.PITCH_Selected := Flight_Modes_PITCH_Selected;
      Bus_Creator_out1.PITCH_Active := Flight_Modes_PITCH_Active;
      Bus_Creator_out1.VS_Selected := Flight_Modes_VS_Selected;
      Bus_Creator_out1.VS_Active := Flight_Modes_VS_Active;
      Bus_Creator_out1.FLC_Selected := Flight_Modes_FLC_Selected;
      Bus_Creator_out1.FLC_Active := Flight_Modes_FLC_Active;
      Bus_Creator_out1.ALT_Selected := Flight_Modes_ALT_Selected;
      Bus_Creator_out1.ALT_Active := Flight_Modes_ALT_Active;
      Bus_Creator_out1.ALTSEL_Selected := Flight_Modes_ALTSEL_Selected;
      Bus_Creator_out1.ALTSEL_Active := Flight_Modes_ALTSEL_Active;
      Bus_Creator_out1.ALTSEL_Track := Flight_Modes_ALTSEL_Track;
      Bus_Creator_out1.VAPPR_Selected := Flight_Modes_VAPPR_Selected;
      Bus_Creator_out1.VAPPR_Active := Flight_Modes_VAPPR_Active;
      Bus_Creator_out1.VGA_Selected := Flight_Modes_VGA_Selected;
      Bus_Creator_out1.VGA_Active := Flight_Modes_VGA_Active;
      --  End Block Mode_Logic_Props/Bus\nCreator

      --  Block Mode_Logic_Props/Requirements
      Requirements.comp (Inputs_out1, Bus_Creator_out1);
      --  End Block Mode_Logic_Props/Requirements

      --  update Mode_Logic_Props/Mode_Logic/Event_Processing
      Event_Processing.up;
      --  End update Mode_Logic_Props/Mode_Logic/Event_Processing

      --  update Mode_Logic_Props/Requirements
      Requirements.up;
      --  End update Mode_Logic_Props/Requirements
   end comp;

   procedure initStates is
   begin
      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing
      Event_Processing.initStates;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing

      --  Block Mode_Logic_Props/Mode_Logic/Flight_Modes
      Flight_Modes.initStates;
      --  End Block Mode_Logic_Props/Mode_Logic/Flight_Modes

      --  Block Mode_Logic_Props/Requirements
      Requirements.initStates;
      --  End Block Mode_Logic_Props/Requirements
   end initStates;

   procedure initOutputs is
   begin
      --  Block Mode_Logic_Props/Mode_Logic/Flight_Modes
      Flight_Modes.initOutputs (Flight_Modes_Modes_On, Flight_Modes_FD_On, Flight_Modes_Independent_Mode, Flight_Modes_Active_Side, Flight_Modes_ROLL_Selected, Flight_Modes_ROLL_Active, Flight_Modes_HDG_Selected, Flight_Modes_HDG_Active, Flight_Modes_NAV_Selected, Flight_Modes_NAV_Active, Flight_Modes_LAPPR_Selected, Flight_Modes_LAPPR_Active, Flight_Modes_LGA_Selected, Flight_Modes_LGA_Active, Flight_Modes_PITCH_Selected, Flight_Modes_PITCH_Active, Flight_Modes_VS_Selected, Flight_Modes_VS_Active, Flight_Modes_FLC_Selected, Flight_Modes_FLC_Active, Flight_Modes_ALT_Selected, Flight_Modes_ALT_Active, Flight_Modes_ALTSEL_Selected, Flight_Modes_ALTSEL_Active, Flight_Modes_ALTSEL_Track, Flight_Modes_VAPPR_Selected, Flight_Modes_VAPPR_Active, Flight_Modes_VGA_Selected, Flight_Modes_VGA_Active);
      --  End Block Mode_Logic_Props/Mode_Logic/Flight_Modes
   end initOutputs;
end Mode_Logic_Props;
--  @EOF
