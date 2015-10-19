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

with AP_Engaged_Implies_Modes_On; use AP_Engaged_Implies_Modes_On;
with At_Most_One_Lateral_Mode_Active; use At_Most_One_Lateral_Mode_Active;
with Onside_FD_Implies_Modes_On; use Onside_FD_Implies_Modes_On;
with No_Higher_Event_1; use No_Higher_Event_1;
with Modes_On_Iff_FD_On_or_AP_Engaged; use Modes_On_Iff_FD_On_or_AP_Engaged;
with Modes_Off_At_Startup; use Modes_Off_At_Startup;
with Offside_FD_On_Implies_Modes_On; use Offside_FD_On_Implies_Modes_On;
with At_Least_One_Lateral_Mode_Active; use At_Least_One_Lateral_Mode_Active;
with NAV_Active_When_Capture_Cond_Met; use NAV_Active_When_Capture_Cond_Met;

package body Requirements is
   NAV_Selected : Boolean;
   NAV_Active : Boolean;
   Modes_On : Boolean;

   procedure initStates is
   begin
      --  Block Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On
      AP_Engaged_Implies_Modes_On.initStates;
      --  End Block Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On

      --  Block Mode_Logic_Props/Requirements/Modes_Off_At_Startup
      Modes_Off_At_Startup.initStates;
      --  End Block Mode_Logic_Props/Requirements/Modes_Off_At_Startup

      --  Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged
      Modes_On_Iff_FD_On_or_AP_Engaged.initStates;
      --  End Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event
      No_Higher_Event_1.initStates;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event

      --  Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met
      NAV_Active_When_Capture_Cond_Met.initStates;
      --  End Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met

      --  Block Mode_Logic_Props/Requirements/Offside_FD_On_Implies_Modes_On
      Offside_FD_On_Implies_Modes_On.initStates;
      --  End Block Mode_Logic_Props/Requirements/Offside_FD_On_Implies_Modes_On
   end initStates;

   procedure comp
      (Inputs : mode_logic_inputs;
       Outputs : mode_logic_outputs)
   is
      use type Boolean;
      use type Boolean_Array_15;
      use type mode_logic_inputs;
      use type mode_logic_outputs;
      Inputs_out1 : mode_logic_inputs;
      Offside_FD_On : Boolean;
      Is_AP_Engaged : Boolean;
      Pilot_Flying_Side : Boolean;
      Selected_Nav_Source_Changed : Boolean;
      Selected_Nav_Frequency_Changed : Boolean;
      NAV_Capture_Cond_Met : Boolean;
      Is_AP_Engaged_1 : Boolean;
      Offside_FD_On_1 : Boolean;
      Outputs_out1 : mode_logic_outputs;
      FD_On : Boolean;
      Modes_On_1 : Boolean;
      FD_On_1 : Boolean;
      Modes_On_1_1 : Boolean;
      ROLL_Active : Boolean;
      HDG_Active : Boolean;
      NAV_Active_1 : Boolean;
      LAPPR_Active : Boolean;
      LGA_Active : Boolean;
      ROLL_Active_1 : Boolean;
      HDG_Active_1 : Boolean;
      NAV_Active_1_1 : Boolean;
      LAPPR_Active_1 : Boolean;
      LGA_Active_1 : Boolean;
      Modes_On_2 : Boolean;
      Modes_On_3 : Boolean;
      Modes_On_4 : Boolean;
      No_Higher_Event_O : Boolean_Array_15;
      No_Higher_Event_Than_NAV_Capture_Cond_Met : Boolean;
   begin
      --  Block Mode_Logic_Props/Requirements/Inputs
      Inputs_out1 := Inputs;
      --  End Block Mode_Logic_Props/Requirements/Inputs

      --  Block Mode_Logic_Props/Requirements/Bus\nSelector11
      Offside_FD_On := Inputs_out1.Offside_FD_On;
      Is_AP_Engaged := Inputs_out1.Is_AP_Engaged;
      --  End Block Mode_Logic_Props/Requirements/Bus\nSelector11

      --  Block Mode_Logic_Props/Requirements/Bus\nSelector13
      Pilot_Flying_Side := Inputs_out1.Pilot_Flying_Side;
      Selected_Nav_Source_Changed := Inputs_out1.Selected_Nav_Source_Changed;
      Selected_Nav_Frequency_Changed := Inputs_out1.Selected_Nav_Frequency_Changed;
      NAV_Capture_Cond_Met := Inputs_out1.NAV_Capture_Cond_Met;
      --  End Block Mode_Logic_Props/Requirements/Bus\nSelector13

      --  Block Mode_Logic_Props/Requirements/Bus\nSelector7
      Is_AP_Engaged_1 := Inputs_out1.Is_AP_Engaged;
      --  End Block Mode_Logic_Props/Requirements/Bus\nSelector7

      --  Block Mode_Logic_Props/Requirements/Bus\nSelector9
      Offside_FD_On_1 := Inputs_out1.Offside_FD_On;
      --  End Block Mode_Logic_Props/Requirements/Bus\nSelector9

      --  Block Mode_Logic_Props/Requirements/Outputs
      Outputs_out1 := Outputs;
      --  End Block Mode_Logic_Props/Requirements/Outputs

      --  Block Mode_Logic_Props/Requirements/Bus\nSelector10
      FD_On := Outputs_out1.FD_On;
      Modes_On_1 := Outputs_out1.Modes_On;
      --  End Block Mode_Logic_Props/Requirements/Bus\nSelector10

      --  Block Mode_Logic_Props/Requirements/Bus\nSelector12
      NAV_Selected := Outputs_out1.NAV_Selected;
      NAV_Active := Outputs_out1.NAV_Active;
      Modes_On := Outputs_out1.Modes_On;
      --  End Block Mode_Logic_Props/Requirements/Bus\nSelector12

      --  Block Mode_Logic_Props/Requirements/Bus\nSelector2
      FD_On_1 := Outputs_out1.FD_On;
      Modes_On_1_1 := Outputs_out1.Modes_On;
      --  End Block Mode_Logic_Props/Requirements/Bus\nSelector2

      --  Block Mode_Logic_Props/Requirements/Bus\nSelector3
      ROLL_Active := Outputs_out1.ROLL_Active;
      HDG_Active := Outputs_out1.HDG_Active;
      NAV_Active_1 := Outputs_out1.NAV_Active;
      LAPPR_Active := Outputs_out1.LAPPR_Active;
      LGA_Active := Outputs_out1.LGA_Active;
      --  End Block Mode_Logic_Props/Requirements/Bus\nSelector3

      --  Block Mode_Logic_Props/Requirements/Bus\nSelector4
      ROLL_Active_1 := Outputs_out1.ROLL_Active;
      HDG_Active_1 := Outputs_out1.HDG_Active;
      NAV_Active_1_1 := Outputs_out1.NAV_Active;
      LAPPR_Active_1 := Outputs_out1.LAPPR_Active;
      LGA_Active_1 := Outputs_out1.LGA_Active;
      --  End Block Mode_Logic_Props/Requirements/Bus\nSelector4

      --  Block Mode_Logic_Props/Requirements/Bus\nSelector5
      Modes_On_2 := Outputs_out1.Modes_On;
      --  End Block Mode_Logic_Props/Requirements/Bus\nSelector5

      --  Block Mode_Logic_Props/Requirements/Bus\nSelector6
      Modes_On_3 := Outputs_out1.Modes_On;
      --  End Block Mode_Logic_Props/Requirements/Bus\nSelector6

      --  Block Mode_Logic_Props/Requirements/Bus\nSelector8
      Modes_On_4 := Outputs_out1.Modes_On;
      --  End Block Mode_Logic_Props/Requirements/Bus\nSelector8

      --  Block Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On
      AP_Engaged_Implies_Modes_On.comp (Is_AP_Engaged_1, Modes_On_3);
      --  End Block Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On

      --  Block Mode_Logic_Props/Requirements/At_Least_One_Lateral_Mode_Active
      At_Least_One_Lateral_Mode_Active.comp (ROLL_Active_1, HDG_Active_1, NAV_Active_1_1, LAPPR_Active_1, LGA_Active_1);
      --  End Block Mode_Logic_Props/Requirements/At_Least_One_Lateral_Mode_Active

      --  Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active
      At_Most_One_Lateral_Mode_Active.comp (ROLL_Active, HDG_Active, NAV_Active_1, LAPPR_Active, LGA_Active);
      --  End Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active

      --  Block Mode_Logic_Props/Requirements/Modes_Off_At_Startup
      Modes_Off_At_Startup.comp (Modes_On_2);
      --  End Block Mode_Logic_Props/Requirements/Modes_Off_At_Startup

      --  Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged
      Modes_On_Iff_FD_On_or_AP_Engaged.comp (Offside_FD_On, Is_AP_Engaged, FD_On, Modes_On_1);
      --  End Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event
      No_Higher_Event_1.comp (Inputs_out1, No_Higher_Event_O);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event

      --  Block Mode_Logic_Props/Requirements/Bus\nSelector14
      No_Higher_Event_Than_NAV_Capture_Cond_Met := No_Higher_Event_O (11);
      --  End Block Mode_Logic_Props/Requirements/Bus\nSelector14

      --  Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met
      NAV_Active_When_Capture_Cond_Met.comp (Pilot_Flying_Side, Selected_Nav_Source_Changed, Selected_Nav_Frequency_Changed, NAV_Capture_Cond_Met, No_Higher_Event_Than_NAV_Capture_Cond_Met, NAV_Active, Modes_On);
      --  End Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met

      --  Block Mode_Logic_Props/Requirements/Offside_FD_On_Implies_Modes_On
      Offside_FD_On_Implies_Modes_On.comp (Offside_FD_On_1, Modes_On_4);
      --  End Block Mode_Logic_Props/Requirements/Offside_FD_On_Implies_Modes_On

      --  Block Mode_Logic_Props/Requirements/Onside_FD_Implies_Modes_On
      Onside_FD_Implies_Modes_On.comp (FD_On_1, Modes_On_1_1);
      --  End Block Mode_Logic_Props/Requirements/Onside_FD_Implies_Modes_On
   end comp;

   procedure up is
   begin
      --  update Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On
      AP_Engaged_Implies_Modes_On.up;
      --  End update Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On

      --  update Mode_Logic_Props/Requirements/Modes_Off_At_Startup
      Modes_Off_At_Startup.up;
      --  End update Mode_Logic_Props/Requirements/Modes_Off_At_Startup

      --  update Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged
      Modes_On_Iff_FD_On_or_AP_Engaged.up;
      --  End update Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged

      --  update Mode_Logic_Props/Requirements/No_Higher_Event
      No_Higher_Event_1.up;
      --  End update Mode_Logic_Props/Requirements/No_Higher_Event

      --  update Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met
      NAV_Active_When_Capture_Cond_Met.up (NAV_Selected);
      --  End update Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met

      --  update Mode_Logic_Props/Requirements/Offside_FD_On_Implies_Modes_On
      Offside_FD_On_Implies_Modes_On.up;
      --  End update Mode_Logic_Props/Requirements/Offside_FD_On_Implies_Modes_On
   end up;
end Requirements;
--  @EOF
