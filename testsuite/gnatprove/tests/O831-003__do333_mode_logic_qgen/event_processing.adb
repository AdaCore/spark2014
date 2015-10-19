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

with Seen; use Seen;
with Changed; use Changed;
with Rising_Edge; use Rising_Edge;

package body Event_Processing is
   Rising_Edge_memory : Rising_Edge_State;
   Rising_Edge_memory_1 : Rising_Edge_State;
   Rising_Edge_memory_2 : Rising_Edge_State;
   Rising_Edge_memory_3 : Rising_Edge_State;
   Rising_Edge_memory_4 : Rising_Edge_State;
   Rising_Edge_memory_5 : Rising_Edge_State;
   Rising_Edge_memory_6 : Rising_Edge_State;
   Rising_Edge_memory_7 : Rising_Edge_State;
   Rising_Edge_memory_8 : Rising_Edge_State;
   Rising_Edge_memory_9 : Rising_Edge_State;
   Rising_Edge_memory_10 : Rising_Edge_State;
   Rising_Edge_memory_11 : Rising_Edge_State;
   Changed_memory : Changed_State;

   procedure initStates is
   begin
      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Changed PF
      Changed.initStates (Changed_memory);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Changed PF

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALT
      Rising_Edge.initStates (Rising_Edge_memory);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALT

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALTSEL
      Rising_Edge.initStates (Rising_Edge_memory_1);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALTSEL

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge AP
      Rising_Edge.initStates (Rising_Edge_memory_2);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge AP

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge APPR
      Rising_Edge.initStates (Rising_Edge_memory_3);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge APPR

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge FD
      Rising_Edge.initStates (Rising_Edge_memory_4);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge FD

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge FLC
      Rising_Edge.initStates (Rising_Edge_memory_5);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge FLC

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge GA
      Rising_Edge.initStates (Rising_Edge_memory_6);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge GA

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge HDG
      Rising_Edge.initStates (Rising_Edge_memory_7);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge HDG

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge NAV
      Rising_Edge.initStates (Rising_Edge_memory_8);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge NAV

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge SYNC
      Rising_Edge.initStates (Rising_Edge_memory_9);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge SYNC

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge VS Pitch Wheel
      Rising_Edge.initStates (Rising_Edge_memory_10);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge VS Pitch Wheel

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge VS
      Rising_Edge.initStates (Rising_Edge_memory_11);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge VS
   end initStates;

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
       If_VAPPR_Capture_Cond_Met_Seen : out Boolean)
   is
      use type Boolean;
      ALTSEL_Capture_Cond_Met_out1 : Boolean;
      ALTSEL_Target_Changed_out1 : Boolean;
      ALTSEL_Track_Cond_Met_out1 : Boolean;
      ALT_Switch_out1 : Boolean;
      APPR_Switch_out1 : Boolean;
      AP_Engaged_out1 : Boolean;
      FD_Switch_out1 : Boolean;
      FLC_Switch_out1 : Boolean;
      GA_Switch_out1 : Boolean;
      HDG_Switch_out1 : Boolean;
      Is_Pilot_Flying_Side_out1 : Boolean;
      Changed_Out1 : Boolean;
      LAPPR_Capture_Cond_Met_out1 : Boolean;
      NAV_Capture_Cond_Met_out1 : Boolean;
      NAV_Switch_out1 : Boolean;
      Rising_Edge_Out1 : Boolean;
      Rising_Edge_1_Out1 : Boolean;
      Rising_Edge_2_Out1 : Boolean;
      Rising_Edge_3_Out1 : Boolean;
      Rising_Edge_4_Out1 : Boolean;
      Rising_Edge_5_Out1 : Boolean;
      Rising_Edge_6_Out1 : Boolean;
      Rising_Edge_7_Out1 : Boolean;
      Rising_Edge_8_Out1 : Boolean;
      SYNC_Switch_out1 : Boolean;
      Rising_Edge_9_Out1 : Boolean;
      VAPPR_Capture_Cond_Met_out1 : Boolean;
      VS_Pitch_Wheel_Rotated_out1 : Boolean;
      Rising_Edge_11_Out1 : Boolean;
      VS_Switch_out1 : Boolean;
      Rising_Edge_10_Out1 : Boolean;
      False_out1 : Boolean;
      Seen_13_Seen : Boolean;
      Seen_13_Inhibit_Out : Boolean;
      Seen_8_Seen : Boolean;
      Seen_8_Inhibit_Out : Boolean;
      Seen_4_Seen : Boolean;
      Seen_4_Inhibit_Out : Boolean;
      Seen_1_Seen : Boolean;
      Seen_1_Inhibit_Out : Boolean;
      Seen_3_Seen : Boolean;
      Seen_3_Inhibit_Out : Boolean;
      Seen_7_Seen : Boolean;
      Seen_7_Inhibit_Out : Boolean;
      Seen_16_Seen : Boolean;
      Seen_16_Inhibit_Out : Boolean;
      Seen_15_Seen : Boolean;
      Seen_15_Inhibit_Out : Boolean;
      Seen_9_Seen : Boolean;
      Seen_9_Inhibit_Out : Boolean;
      Seen_12_Seen : Boolean;
      Seen_12_Inhibit_Out : Boolean;
      False1_out1 : Boolean;
      Seen_5_Seen : Boolean;
      Seen_5_Inhibit_Out : Boolean;
      OR3_out1 : Boolean;
      Seen_6_Seen : Boolean;
      Seen_6_Inhibit_Out : Boolean;
      Seen_10_Seen : Boolean;
      Seen_10_Inhibit_Out : Boolean;
      Seen_11_Seen : Boolean;
      Seen_11_Inhibit_Out : Boolean;
      pragma Unreferenced (Seen_11_Inhibit_Out);
      Seen_14_Seen : Boolean;
      Seen_14_Inhibit_Out : Boolean;
      Seen_2_Seen : Boolean;
      Seen_2_Inhibit_Out : Boolean;
      Seen_Seen : Boolean;
      Seen_Inhibit_Out : Boolean;
      pragma Unreferenced (Seen_Inhibit_Out);
   begin
      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Capture_Cond_Met
      ALTSEL_Capture_Cond_Met_out1 := ALTSEL_Capture_Cond_Met;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Capture_Cond_Met

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Target_Changed
      ALTSEL_Target_Changed_out1 := ALTSEL_Target_Changed;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Target_Changed

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Track_Cond_Met
      ALTSEL_Track_Cond_Met_out1 := ALTSEL_Track_Cond_Met;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Track_Cond_Met

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALT_Switch
      ALT_Switch_out1 := ALT_Switch;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALT_Switch

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/APPR_Switch
      APPR_Switch_out1 := APPR_Switch;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/APPR_Switch

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/AP_Engaged
      AP_Engaged_out1 := AP_Engaged;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/AP_Engaged

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/FD_Switch
      FD_Switch_out1 := FD_Switch;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/FD_Switch

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/FLC_Switch
      FLC_Switch_out1 := FLC_Switch;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/FLC_Switch

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/GA_Switch
      GA_Switch_out1 := GA_Switch;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/GA_Switch

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/HDG_Switch
      HDG_Switch_out1 := HDG_Switch;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/HDG_Switch

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Is_Pilot_Flying_Side
      Is_Pilot_Flying_Side_out1 := Is_Pilot_Flying_Side;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Is_Pilot_Flying_Side

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Changed PF
      Changed.comp (Is_Pilot_Flying_Side_out1, Changed_Out1, Changed_memory);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Changed PF

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/LAPPR_Capture_Cond_Met
      LAPPR_Capture_Cond_Met_out1 := LAPPR_Capture_Cond_Met;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/LAPPR_Capture_Cond_Met

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/NAV_Capture_Cond_Met
      NAV_Capture_Cond_Met_out1 := NAV_Capture_Cond_Met;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/NAV_Capture_Cond_Met

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/NAV_Switch
      NAV_Switch_out1 := NAV_Switch;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/NAV_Switch

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALT
      Rising_Edge.comp (ALT_Switch_out1, Rising_Edge_Out1, Rising_Edge_memory);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALT

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALTSEL
      Rising_Edge.comp (ALTSEL_Target_Changed_out1, Rising_Edge_1_Out1, Rising_Edge_memory_1);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALTSEL

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge AP
      Rising_Edge.comp (AP_Engaged_out1, Rising_Edge_2_Out1, Rising_Edge_memory_2);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge AP

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge APPR
      Rising_Edge.comp (APPR_Switch_out1, Rising_Edge_3_Out1, Rising_Edge_memory_3);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge APPR

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge FD
      Rising_Edge.comp (FD_Switch_out1, Rising_Edge_4_Out1, Rising_Edge_memory_4);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge FD

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge FLC
      Rising_Edge.comp (FLC_Switch_out1, Rising_Edge_5_Out1, Rising_Edge_memory_5);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge FLC

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge GA
      Rising_Edge.comp (GA_Switch_out1, Rising_Edge_6_Out1, Rising_Edge_memory_6);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge GA

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge HDG
      Rising_Edge.comp (HDG_Switch_out1, Rising_Edge_7_Out1, Rising_Edge_memory_7);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge HDG

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge NAV
      Rising_Edge.comp (NAV_Switch_out1, Rising_Edge_8_Out1, Rising_Edge_memory_8);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge NAV

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/SYNC_Switch
      SYNC_Switch_out1 := SYNC_Switch;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/SYNC_Switch

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge SYNC
      Rising_Edge.comp (SYNC_Switch_out1, Rising_Edge_9_Out1, Rising_Edge_memory_9);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge SYNC

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/VAPPR_Capture_Cond_Met
      VAPPR_Capture_Cond_Met_out1 := VAPPR_Capture_Cond_Met;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/VAPPR_Capture_Cond_Met

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/VS_Pitch_Wheel_Rotated
      VS_Pitch_Wheel_Rotated_out1 := VS_Pitch_Wheel_Rotated;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/VS_Pitch_Wheel_Rotated

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge VS Pitch Wheel
      Rising_Edge.comp (VS_Pitch_Wheel_Rotated_out1, Rising_Edge_11_Out1, Rising_Edge_memory_10);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge VS Pitch Wheel

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/VS_Switch
      VS_Switch_out1 := VS_Switch;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/VS_Switch

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge VS
      Rising_Edge.comp (VS_Switch_out1, Rising_Edge_10_Out1, Rising_Edge_memory_11);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge VS

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_Pilot_Fllying_Transfer_Seen
      When_Pilot_Fllying_Transfer_Seen := Changed_Out1;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_Pilot_Fllying_Transfer_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/False
      False_out1 := False;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/False

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/SYNC_Switch_Pressed_Seen
      Seen.comp (False_out1, Rising_Edge_9_Out1, Seen_13_Seen, Seen_13_Inhibit_Out);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/SYNC_Switch_Pressed_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/GA_Switch_Pressed_Seen
      Seen.comp (Seen_13_Inhibit_Out, Rising_Edge_6_Out1, Seen_8_Seen, Seen_8_Inhibit_Out);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/GA_Switch_Pressed_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/APPR_Switch_Pressed_Seen
      Seen.comp (Seen_8_Inhibit_Out, Rising_Edge_3_Out1, Seen_4_Seen, Seen_4_Inhibit_Out);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/APPR_Switch_Pressed_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Target_Changed_Seen
      Seen.comp (Seen_4_Inhibit_Out, Rising_Edge_1_Out1, Seen_1_Seen, Seen_1_Inhibit_Out);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Target_Changed_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALT_Switch_Pressed_Seen
      Seen.comp (Seen_1_Inhibit_Out, Rising_Edge_Out1, Seen_3_Seen, Seen_3_Inhibit_Out);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALT_Switch_Pressed_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/FLC_Switch_Pressed_Seen
      Seen.comp (Seen_3_Inhibit_Out, Rising_Edge_5_Out1, Seen_7_Seen, Seen_7_Inhibit_Out);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/FLC_Switch_Pressed_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/VS_Switch_Pressed_Seen
      Seen.comp (Seen_7_Inhibit_Out, Rising_Edge_10_Out1, Seen_16_Seen, Seen_16_Inhibit_Out);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/VS_Switch_Pressed_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/VS_Pitch_Wheel_Rotated_Seen
      Seen.comp (Seen_16_Inhibit_Out, Rising_Edge_11_Out1, Seen_15_Seen, Seen_15_Inhibit_Out);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/VS_Pitch_Wheel_Rotated_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/HDG_Switch_Presssed_Seen
      Seen.comp (Seen_4_Inhibit_Out, Rising_Edge_7_Out1, Seen_9_Seen, Seen_9_Inhibit_Out);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/HDG_Switch_Presssed_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/NAV_Switch_Pressed_Seen
      Seen.comp (Seen_9_Inhibit_Out, Rising_Edge_8_Out1, Seen_12_Seen, Seen_12_Inhibit_Out);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/NAV_Switch_Pressed_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_ALTSEL_Target_Changed_Seen
      When_ALTSEL_Target_Changed_Seen := Seen_1_Seen;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_ALTSEL_Target_Changed_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_ALT_Switch_Pressed_Seen
      When_ALT_Switch_Pressed_Seen := Seen_3_Seen;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_ALT_Switch_Pressed_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_APPR_Switch_Pressed_Seen
      When_APPR_Switch_Pressed_Seen := Seen_4_Seen;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_APPR_Switch_Pressed_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_FLC_Switch_Pressed_Seen
      When_FLC_Switch_Pressed_Seen := Seen_7_Seen;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_FLC_Switch_Pressed_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_GA_Switch_Pressed_Seen
      When_GA_Switch_Pressed_Seen := Seen_8_Seen;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_GA_Switch_Pressed_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_HDG_Switch_Pressed_Seen
      When_HDG_Switch_Pressed_Seen := Seen_9_Seen;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_HDG_Switch_Pressed_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_NAV_Switch_Pressed_Seen
      When_NAV_Switch_Pressed_Seen := Seen_12_Seen;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_NAV_Switch_Pressed_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_SYNC_Switch_Pressed_Seen
      When_SYNC_Switch_Pressed_Seen := Seen_13_Seen;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_SYNC_Switch_Pressed_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_VS_Pitch_Wheel_Rotated_Seen
      When_VS_Pitch_Wheel_Rotated_Seen := Seen_15_Seen;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_VS_Pitch_Wheel_Rotated_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_VS_Switch_Pressed_Seen
      When_VS_Switch_Pressed_Seen := Seen_16_Seen;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_VS_Switch_Pressed_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/False1
      False1_out1 := False;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/False1

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/AP_Engaged_Seen
      Seen.comp (False1_out1, Rising_Edge_2_Out1, Seen_5_Seen, Seen_5_Inhibit_Out);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/AP_Engaged_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_AP_Engaged_Seen
      When_AP_Engaged_Seen := Seen_5_Seen;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_AP_Engaged_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/OR3
      OR3_out1 := ((Seen_12_Inhibit_Out)
         or else (Seen_5_Inhibit_Out))
            or else (Seen_15_Inhibit_Out);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/OR3

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/FD_Switch_Pressed_Seen
      Seen.comp (OR3_out1, Rising_Edge_4_Out1, Seen_6_Seen, Seen_6_Inhibit_Out);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/FD_Switch_Pressed_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/LAPPR_Capture_Cond_Met_Seen
      Seen.comp (Seen_6_Inhibit_Out, LAPPR_Capture_Cond_Met_out1, Seen_10_Seen, Seen_10_Inhibit_Out);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/LAPPR_Capture_Cond_Met_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/If_LAPPR_Capture_Cond_Met_Seen
      If_LAPPR_Capture_Cond_Met_Seen := Seen_10_Seen;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/If_LAPPR_Capture_Cond_Met_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/NAV_Capture_Cond_Met_Seen
      Seen.comp (Seen_10_Inhibit_Out, NAV_Capture_Cond_Met_out1, Seen_11_Seen, Seen_11_Inhibit_Out);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/NAV_Capture_Cond_Met_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/If_NAV_Capture_Cond_Met_Seen
      If_NAV_Capture_Cond_Met_Seen := Seen_11_Seen;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/If_NAV_Capture_Cond_Met_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/VAPPR_Capture_Cond_Met_Seen
      Seen.comp (Seen_6_Inhibit_Out, VAPPR_Capture_Cond_Met_out1, Seen_14_Seen, Seen_14_Inhibit_Out);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/VAPPR_Capture_Cond_Met_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/If_VAPPR_Capture_Cond_Met_Seen
      If_VAPPR_Capture_Cond_Met_Seen := Seen_14_Seen;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/If_VAPPR_Capture_Cond_Met_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Track_Cond_Met_Seen
      Seen.comp (Seen_14_Inhibit_Out, ALTSEL_Track_Cond_Met_out1, Seen_2_Seen, Seen_2_Inhibit_Out);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Track_Cond_Met_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/If_ALTSEL_Track_Cond_Met_Seen
      If_ALTSEL_Track_Cond_Met_Seen := Seen_2_Seen;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/If_ALTSEL_Track_Cond_Met_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Capture_Cond_Met_Seen
      Seen.comp (Seen_2_Inhibit_Out, ALTSEL_Capture_Cond_Met_out1, Seen_Seen, Seen_Inhibit_Out);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Capture_Cond_Met_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/If_ALTSEL_Capture_Cond_Met_Seen
      If_ALTSEL_Capture_Cond_Met_Seen := Seen_Seen;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/If_ALTSEL_Capture_Cond_Met_Seen

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_FD_Switch_Pressed_Seen
      When_FD_Switch_Pressed_Seen := Seen_6_Seen;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/When_FD_Switch_Pressed_Seen
   end comp;

   procedure up is
   begin
      --  update Mode_Logic_Props/Mode_Logic/Event_Processing/Changed PF
      Changed.up (Changed_memory);
      --  End update Mode_Logic_Props/Mode_Logic/Event_Processing/Changed PF

      --  update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALT
      Rising_Edge.up (Rising_Edge_memory);
      --  End update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALT

      --  update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALTSEL
      Rising_Edge.up (Rising_Edge_memory_1);
      --  End update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALTSEL

      --  update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge AP
      Rising_Edge.up (Rising_Edge_memory_2);
      --  End update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge AP

      --  update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge APPR
      Rising_Edge.up (Rising_Edge_memory_3);
      --  End update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge APPR

      --  update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge FD
      Rising_Edge.up (Rising_Edge_memory_4);
      --  End update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge FD

      --  update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge FLC
      Rising_Edge.up (Rising_Edge_memory_5);
      --  End update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge FLC

      --  update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge GA
      Rising_Edge.up (Rising_Edge_memory_6);
      --  End update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge GA

      --  update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge HDG
      Rising_Edge.up (Rising_Edge_memory_7);
      --  End update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge HDG

      --  update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge NAV
      Rising_Edge.up (Rising_Edge_memory_8);
      --  End update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge NAV

      --  update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge SYNC
      Rising_Edge.up (Rising_Edge_memory_9);
      --  End update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge SYNC

      --  update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge VS Pitch Wheel
      Rising_Edge.up (Rising_Edge_memory_10);
      --  End update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge VS Pitch Wheel

      --  update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge VS
      Rising_Edge.up (Rising_Edge_memory_11);
      --  End update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge VS
   end up;
end Event_Processing;
--  @EOF
