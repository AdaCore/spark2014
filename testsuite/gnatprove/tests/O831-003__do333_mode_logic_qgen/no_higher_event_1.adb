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

with No_Higher; use No_Higher;
with Rising_Edge; use Rising_Edge;

package body No_Higher_Event_1 is
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

   procedure initStates is
   begin
      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge ALT
      Rising_Edge.initStates (Rising_Edge_memory);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge ALT

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge ALTSEL
      Rising_Edge.initStates (Rising_Edge_memory_1);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge ALTSEL

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge AP
      Rising_Edge.initStates (Rising_Edge_memory_2);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge AP

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge APPR
      Rising_Edge.initStates (Rising_Edge_memory_3);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge APPR

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge FD
      Rising_Edge.initStates (Rising_Edge_memory_4);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge FD

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge FLC
      Rising_Edge.initStates (Rising_Edge_memory_5);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge FLC

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge GA
      Rising_Edge.initStates (Rising_Edge_memory_6);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge GA

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge HDG
      Rising_Edge.initStates (Rising_Edge_memory_7);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge HDG

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge NAV
      Rising_Edge.initStates (Rising_Edge_memory_8);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge NAV

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge SYNC
      Rising_Edge.initStates (Rising_Edge_memory_9);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge SYNC

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge VS
      Rising_Edge.initStates (Rising_Edge_memory_10);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge VS

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge VS Pitch Wheel
      Rising_Edge.initStates (Rising_Edge_memory_11);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge VS Pitch Wheel
   end initStates;

   procedure comp (I : mode_logic_inputs; O : out Boolean_Array_15) is
      use type Boolean;
      use type Boolean_Array_15;
      use type mode_logic_inputs;
      I_out1 : mode_logic_inputs;
      Bus_Selector_out1 : Boolean;
      Bus_Selector1_out1 : Boolean;
      Bus_Selector10_out1 : Boolean;
      Bus_Selector11_out1 : Boolean;
      Bus_Selector12_out1 : Boolean;
      Bus_Selector13_out1 : Boolean;
      Bus_Selector14_out1 : Boolean;
      Bus_Selector15_out1 : Boolean;
      Bus_Selector16_out1 : Boolean;
      Bus_Selector2_out1 : Boolean;
      Bus_Selector3_out1 : Boolean;
      Bus_Selector4_out1 : Boolean;
      Bus_Selector5_out1 : Boolean;
      Bus_Selector6_out1 : Boolean;
      Bus_Selector7_out1 : Boolean;
      Bus_Selector8_out1 : Boolean;
      Bus_Selector9_out1 : Boolean;
      Rising_Edge_Out1 : Boolean;
      Rising_Edge_Out1_1 : Boolean;
      Rising_Edge_Out1_2 : Boolean;
      Rising_Edge_Out1_3 : Boolean;
      Rising_Edge_Out1_4 : Boolean;
      Rising_Edge_Out1_5 : Boolean;
      Rising_Edge_Out1_6 : Boolean;
      Rising_Edge_Out1_7 : Boolean;
      Rising_Edge_Out1_8 : Boolean;
      Rising_Edge_Out1_9 : Boolean;
      Rising_Edge_Out1_10 : Boolean;
      Rising_Edge_Out1_11 : Boolean;
      False_out1 : Boolean;
      No_Higher_Event_Than_SYNC_Switch_Pressed : Boolean;
      No_Higher_No_Higher_Below : Boolean;
      No_Higher_Event_Than_GA_Switch_Pressed : Boolean;
      No_Higher_No_Higher_Below_1 : Boolean;
      No_Higher_Event_Than_APPR_Switch_Pressed : Boolean;
      No_Higher_No_Higher_Below_2 : Boolean;
      No_Higher_Event_Than_ALTSEL_Target_Changed : Boolean;
      No_Higher_No_Higher_Below_3 : Boolean;
      No_Higher_Event_Than_ALT_Switch_Pressed : Boolean;
      No_Higher_No_Higher_Below_4 : Boolean;
      No_Higher_Event_Than_FLC_Switch_Pressed : Boolean;
      No_Higher_No_Higher_Below_5 : Boolean;
      No_Higher_Event_Than_HDG_Switch_Pressed : Boolean;
      No_Higher_No_Higher_Below_6 : Boolean;
      No_Higher_No_Higher : Boolean;
      No_Higher_No_Higher_Below_7 : Boolean;
      No_Higher_Event_Than_VS_Switch_Pressed : Boolean;
      No_Higher_No_Higher_Below_8 : Boolean;
      No_Higher_No_Higher_1 : Boolean;
      No_Higher_No_Higher_Below_9 : Boolean;
      False1_out1 : Boolean;
      No_Higher_Event_Than_AP_Engaged : Boolean;
      No_Higher_No_Higher_Below_10 : Boolean;
      AND_out1 : Boolean;
      No_Higher_Event_Than_FD_Switch_Pressed : Boolean;
      No_Higher_No_Higher_Below_11 : Boolean;
      No_Higher_Event_Than_LAPPR_Capture_Cond_Met : Boolean;
      No_Higher_No_Higher_Below_12 : Boolean;
      No_Higher_Event_Than_NAV_Capture_Cond_Met : Boolean;
      No_Higher_No_Higher_Below_13 : Boolean;
      pragma Unreferenced (No_Higher_No_Higher_Below_13);
      No_Higher_Event_Than_VAPPR_Capture_Cond_Met : Boolean;
      No_Higher_No_Higher_Below_14 : Boolean;
      No_Higher_Event_Than_ALTSEL_Track_Cond_Met : Boolean;
      No_Higher_No_Higher_Below_15 : Boolean;
      No_Higher_Event_Than_ALTSEL_Capture_Cond_Met : Boolean;
      No_Higher_No_Higher_Below_16 : Boolean;
      pragma Unreferenced (No_Higher_No_Higher_Below_16);
      Bus_Creator_out1 : Boolean_Array_15;
   begin
      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/I
      I_out1 := I;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/I

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector
      Bus_Selector_out1 := I_out1.SYNC_Switch;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector1
      Bus_Selector1_out1 := I_out1.GA_Switch;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector1

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector10
      Bus_Selector10_out1 := I_out1.ALTSEL_Target_Changed;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector10

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector11
      Bus_Selector11_out1 := I_out1.Is_AP_Engaged;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector11

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector12
      Bus_Selector12_out1 := I_out1.LAPPR_Capture_Cond_Met;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector12

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector13
      Bus_Selector13_out1 := I_out1.NAV_Capture_Cond_Met;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector13

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector14
      Bus_Selector14_out1 := I_out1.VAPPR_Capture_Cond_Met;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector14

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector15
      Bus_Selector15_out1 := I_out1.ALTSEL_Track_Cond_Met;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector15

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector16
      Bus_Selector16_out1 := I_out1.ALTSEL_Capture_Cond_Met;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector16

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector2
      Bus_Selector2_out1 := I_out1.APPR_Switch;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector2

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector3
      Bus_Selector3_out1 := I_out1.HDG_Switch;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector3

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector4
      Bus_Selector4_out1 := I_out1.NAV_Switch;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector4

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector5
      Bus_Selector5_out1 := I_out1.ALT_Switch;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector5

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector6
      Bus_Selector6_out1 := I_out1.FLC_Switch;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector6

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector7
      Bus_Selector7_out1 := I_out1.VS_Switch;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector7

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector8
      Bus_Selector8_out1 := I_out1.VS_Pitch_Wheel_Rotated;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector8

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector9
      Bus_Selector9_out1 := I_out1.FD_Switch;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nSelector9

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge ALT
      Rising_Edge.comp (Bus_Selector5_out1, Rising_Edge_Out1, Rising_Edge_memory);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge ALT

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge ALTSEL
      Rising_Edge.comp (Bus_Selector10_out1, Rising_Edge_Out1_1, Rising_Edge_memory_1);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge ALTSEL

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge AP
      Rising_Edge.comp (Bus_Selector11_out1, Rising_Edge_Out1_2, Rising_Edge_memory_2);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge AP

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge APPR
      Rising_Edge.comp (Bus_Selector2_out1, Rising_Edge_Out1_3, Rising_Edge_memory_3);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge APPR

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge FD
      Rising_Edge.comp (Bus_Selector9_out1, Rising_Edge_Out1_4, Rising_Edge_memory_4);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge FD

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge FLC
      Rising_Edge.comp (Bus_Selector6_out1, Rising_Edge_Out1_5, Rising_Edge_memory_5);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge FLC

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge GA
      Rising_Edge.comp (Bus_Selector1_out1, Rising_Edge_Out1_6, Rising_Edge_memory_6);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge GA

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge HDG
      Rising_Edge.comp (Bus_Selector3_out1, Rising_Edge_Out1_7, Rising_Edge_memory_7);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge HDG

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge NAV
      Rising_Edge.comp (Bus_Selector4_out1, Rising_Edge_Out1_8, Rising_Edge_memory_8);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge NAV

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge SYNC
      Rising_Edge.comp (Bus_Selector_out1, Rising_Edge_Out1_9, Rising_Edge_memory_9);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge SYNC

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge VS
      Rising_Edge.comp (Bus_Selector7_out1, Rising_Edge_Out1_10, Rising_Edge_memory_10);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge VS

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge VS Pitch Wheel
      Rising_Edge.comp (Bus_Selector8_out1, Rising_Edge_Out1_11, Rising_Edge_memory_11);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge VS Pitch Wheel

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/False
      False_out1 := True;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/False

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_SYNC_Switch
      No_Higher.comp (False_out1, Rising_Edge_Out1_9, No_Higher_Event_Than_SYNC_Switch_Pressed, No_Higher_No_Higher_Below);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_SYNC_Switch

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_GA_Switch
      No_Higher.comp (No_Higher_No_Higher_Below, Rising_Edge_Out1_6, No_Higher_Event_Than_GA_Switch_Pressed, No_Higher_No_Higher_Below_1);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_GA_Switch

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_APPR_Switch
      No_Higher.comp (No_Higher_No_Higher_Below_1, Rising_Edge_Out1_3, No_Higher_Event_Than_APPR_Switch_Pressed, No_Higher_No_Higher_Below_2);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_APPR_Switch

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_ALTSEL_Target_Changed
      No_Higher.comp (No_Higher_No_Higher_Below_2, Rising_Edge_Out1_1, No_Higher_Event_Than_ALTSEL_Target_Changed, No_Higher_No_Higher_Below_3);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_ALTSEL_Target_Changed

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_ALT_Switch
      No_Higher.comp (No_Higher_No_Higher_Below_3, Rising_Edge_Out1, No_Higher_Event_Than_ALT_Switch_Pressed, No_Higher_No_Higher_Below_4);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_ALT_Switch

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_FLC_Switch
      No_Higher.comp (No_Higher_No_Higher_Below_4, Rising_Edge_Out1_5, No_Higher_Event_Than_FLC_Switch_Pressed, No_Higher_No_Higher_Below_5);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_FLC_Switch

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_HDG_Switch
      No_Higher.comp (No_Higher_No_Higher_Below_2, Rising_Edge_Out1_7, No_Higher_Event_Than_HDG_Switch_Pressed, No_Higher_No_Higher_Below_6);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_HDG_Switch

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_NAV_Switch
      No_Higher.comp (No_Higher_No_Higher_Below_6, Rising_Edge_Out1_8, No_Higher_No_Higher, No_Higher_No_Higher_Below_7);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_NAV_Switch

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_VS_Switch
      No_Higher.comp (No_Higher_No_Higher_Below_5, Rising_Edge_Out1_10, No_Higher_Event_Than_VS_Switch_Pressed, No_Higher_No_Higher_Below_8);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_VS_Switch

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_VS_Switch1
      No_Higher.comp (No_Higher_No_Higher_Below_8, Rising_Edge_Out1_11, No_Higher_No_Higher_1, No_Higher_No_Higher_Below_9);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_VS_Switch1

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/False1
      False1_out1 := True;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/False1

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_AP_Engaged
      No_Higher.comp (False1_out1, Rising_Edge_Out1_2, No_Higher_Event_Than_AP_Engaged, No_Higher_No_Higher_Below_10);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_AP_Engaged

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/AND
      AND_out1 := ((No_Higher_No_Higher_Below_7)
         and then (No_Higher_No_Higher_Below_10))
            and then (No_Higher_No_Higher_Below_9);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/AND

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_FD_Switch
      No_Higher.comp (AND_out1, Rising_Edge_Out1_4, No_Higher_Event_Than_FD_Switch_Pressed, No_Higher_No_Higher_Below_11);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_FD_Switch

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_LAPPR_Capture
      No_Higher.comp (No_Higher_No_Higher_Below_11, Bus_Selector12_out1, No_Higher_Event_Than_LAPPR_Capture_Cond_Met, No_Higher_No_Higher_Below_12);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_LAPPR_Capture

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_NAV_Capture
      No_Higher.comp (No_Higher_No_Higher_Below_12, Bus_Selector13_out1, No_Higher_Event_Than_NAV_Capture_Cond_Met, No_Higher_No_Higher_Below_13);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_NAV_Capture

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_VAPPR_Capture
      No_Higher.comp (No_Higher_No_Higher_Below_11, Bus_Selector14_out1, No_Higher_Event_Than_VAPPR_Capture_Cond_Met, No_Higher_No_Higher_Below_14);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_VAPPR_Capture

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_ALTSEL_Track
      No_Higher.comp (No_Higher_No_Higher_Below_14, Bus_Selector15_out1, No_Higher_Event_Than_ALTSEL_Track_Cond_Met, No_Higher_No_Higher_Below_15);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_ALTSEL_Track

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_ALTSEL_Capture
      No_Higher.comp (No_Higher_No_Higher_Below_15, Bus_Selector16_out1, No_Higher_Event_Than_ALTSEL_Capture_Cond_Met, No_Higher_No_Higher_Below_16);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_ALTSEL_Capture

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nCreator
      Bus_Creator_out1 (0) := No_Higher_Event_Than_SYNC_Switch_Pressed;
      Bus_Creator_out1 (1) := No_Higher_Event_Than_GA_Switch_Pressed;
      Bus_Creator_out1 (2) := No_Higher_Event_Than_APPR_Switch_Pressed;
      Bus_Creator_out1 (3) := No_Higher_Event_Than_HDG_Switch_Pressed;
      Bus_Creator_out1 (4) := No_Higher_Event_Than_AP_Engaged;
      Bus_Creator_out1 (5) := No_Higher_Event_Than_ALTSEL_Target_Changed;
      Bus_Creator_out1 (6) := No_Higher_Event_Than_ALT_Switch_Pressed;
      Bus_Creator_out1 (7) := No_Higher_Event_Than_FLC_Switch_Pressed;
      Bus_Creator_out1 (8) := No_Higher_Event_Than_VS_Switch_Pressed;
      Bus_Creator_out1 (9) := No_Higher_Event_Than_FD_Switch_Pressed;
      Bus_Creator_out1 (10) := No_Higher_Event_Than_LAPPR_Capture_Cond_Met;
      Bus_Creator_out1 (11) := No_Higher_Event_Than_NAV_Capture_Cond_Met;
      Bus_Creator_out1 (12) := No_Higher_Event_Than_VAPPR_Capture_Cond_Met;
      Bus_Creator_out1 (13) := No_Higher_Event_Than_ALTSEL_Capture_Cond_Met;
      Bus_Creator_out1 (14) := No_Higher_Event_Than_ALTSEL_Track_Cond_Met;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/Bus\nCreator

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/O

      for i_1 in 0 .. 14 loop
         O (i_1) := Bus_Creator_out1 (i_1);
      end loop;

      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/O
   end comp;

   procedure up is
   begin
      --  update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge ALT
      Rising_Edge.up (Rising_Edge_memory);
      --  End update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge ALT

      --  update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge ALTSEL
      Rising_Edge.up (Rising_Edge_memory_1);
      --  End update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge ALTSEL

      --  update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge AP
      Rising_Edge.up (Rising_Edge_memory_2);
      --  End update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge AP

      --  update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge APPR
      Rising_Edge.up (Rising_Edge_memory_3);
      --  End update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge APPR

      --  update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge FD
      Rising_Edge.up (Rising_Edge_memory_4);
      --  End update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge FD

      --  update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge FLC
      Rising_Edge.up (Rising_Edge_memory_5);
      --  End update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge FLC

      --  update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge GA
      Rising_Edge.up (Rising_Edge_memory_6);
      --  End update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge GA

      --  update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge HDG
      Rising_Edge.up (Rising_Edge_memory_7);
      --  End update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge HDG

      --  update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge NAV
      Rising_Edge.up (Rising_Edge_memory_8);
      --  End update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge NAV

      --  update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge SYNC
      Rising_Edge.up (Rising_Edge_memory_9);
      --  End update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge SYNC

      --  update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge VS
      Rising_Edge.up (Rising_Edge_memory_10);
      --  End update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge VS

      --  update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge VS Pitch Wheel
      Rising_Edge.up (Rising_Edge_memory_11);
      --  End update Mode_Logic_Props/Requirements/No_Higher_Event/Rising Edge VS Pitch Wheel
   end up;
end No_Higher_Event_1;
--  @EOF
