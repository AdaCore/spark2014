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

with Changed; use Changed;

package body NAV_Active_When_Capture_Cond_Met is
   NAV_Active_out1 : Boolean;
   NAV_Selected_out1 : Boolean;
   Unit_Delay_memory : Boolean;
   Unit_Delay1_memory : Boolean;
   Changed_memory : Changed_State;

   procedure initStates is
   begin
      --  Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Unit Delay
      Unit_Delay_memory := False;
      --  End Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Unit Delay

      --  Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Unit Delay1
      Unit_Delay1_memory := False;
      --  End Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Unit Delay1

      --  Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Changed
      Changed.initStates (Changed_memory);
      --  End Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Changed
   end initStates;

   procedure comp
      (Pilot_Flying_Side : Boolean;
       Selected_NAV_Source_Changed : Boolean;
       Selected_NAV_Frequency_Changed : Boolean;
       NAV_Capture_Cond_Met : Boolean;
       No_Higher_Event_Than_NAV_Capture_Cond_Met : Boolean;
       NAV_Active : Boolean;
       Modes_On : Boolean)
   is
      use type Boolean;
      Unit_Delay_out1 : Boolean;
      Unit_Delay1_out1 : Boolean;
      Modes_On_out1 : Boolean;
      NAV_Capture_Cond_Met_out1 : Boolean;
      No_Higher_Event_Than_NAV_Capture_Cond_Met_out1 : Boolean;
      Pilot_Flying_Side_out1 : Boolean;
      Changed_Out1 : Boolean;
      Selected_NAV_Frequency_Changed_out1 : Boolean;
      Selected_NAV_Source_Changed_out1 : Boolean;
      NOT4_out1 : Boolean;
      NOT3_out1 : Boolean;
      NOT2_out1 : Boolean;
      NOT_out1 : Boolean;
      OR_out1 : Boolean;
      NOT1_out1 : Boolean;
      NOT5_out1 : Boolean;
   begin
      --  Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Unit Delay
      Unit_Delay_out1 := Unit_Delay_memory;
      --  End Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Unit Delay

      --  Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Unit Delay1
      Unit_Delay1_out1 := Unit_Delay1_memory;
      --  End Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Unit Delay1

      --  Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Modes_On
      Modes_On_out1 := Modes_On;
      --  End Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Modes_On

      --  Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/NAV_Active
      NAV_Active_out1 := NAV_Active;
      --  End Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/NAV_Active

      --  Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/NAV_Capture_Cond_Met
      NAV_Capture_Cond_Met_out1 := NAV_Capture_Cond_Met;
      --  End Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/NAV_Capture_Cond_Met

      --  Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/No_Higher_Event_Than_NAV_Capture_Cond_Met
      No_Higher_Event_Than_NAV_Capture_Cond_Met_out1 := No_Higher_Event_Than_NAV_Capture_Cond_Met;
      --  End Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/No_Higher_Event_Than_NAV_Capture_Cond_Met

      --  Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Pilot_Flying_Side
      Pilot_Flying_Side_out1 := Pilot_Flying_Side;
      --  End Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Pilot_Flying_Side

      --  Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Changed
      Changed.comp (Pilot_Flying_Side_out1, Changed_Out1, Changed_memory);
      --  End Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Changed

      --  Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Selected_NAV_Frequency_Changed
      Selected_NAV_Frequency_Changed_out1 := Selected_NAV_Frequency_Changed;
      --  End Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Selected_NAV_Frequency_Changed

      --  Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Selected_NAV_Source_Changed
      Selected_NAV_Source_Changed_out1 := Selected_NAV_Source_Changed;
      --  End Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Selected_NAV_Source_Changed

      --  Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/NOT4
      NOT4_out1 := not  (Changed_Out1);
      --  End Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/NOT4

      --  Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/NOT3
      NOT3_out1 := not  (Selected_NAV_Frequency_Changed_out1);
      --  End Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/NOT3

      --  Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/NOT2
      NOT2_out1 := not  (Selected_NAV_Source_Changed_out1);
      --  End Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/NOT2

      --  Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/NOT
      NOT_out1 := not  (Unit_Delay1_out1);
      --  End Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/NOT

      --  Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/OR
      OR_out1 := (((((((Unit_Delay_out1)
         and then (NOT_out1))
            and then (NAV_Capture_Cond_Met_out1))
               and then (NOT2_out1))
                  and then (NOT3_out1))
                     and then (NOT4_out1))
                        and then (Modes_On_out1))
                           and then (No_Higher_Event_Than_NAV_Capture_Cond_Met_out1);
      --  End Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/OR

      --  Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/My_Implies/NOT1
      NOT1_out1 := not  (OR_out1);
      --  End Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/My_Implies/NOT1

      --  Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/My_Implies/NOT5
      NOT5_out1 := (NOT1_out1)
         or else (NAV_Active_out1);
      --  End Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/My_Implies/NOT5

      --  Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/My_Assertion
      pragma Assert (NOT5_out1, "Violation of assertion at block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/My_Assertion");
      --  End Block Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/My_Assertion
   end comp;

   procedure up (NAV_Selected : Boolean) is
      use type Boolean;
   begin
      --  update Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/NAV_Selected
      NAV_Selected_out1 := NAV_Selected;
      --  End update Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/NAV_Selected

      --  update Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Unit Delay
      Unit_Delay_memory := NAV_Selected_out1;
      --  End update Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Unit Delay

      --  update Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Unit Delay1
      Unit_Delay1_memory := NAV_Active_out1;
      --  End update Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Unit Delay1

      --  update Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Changed
      Changed.up (Changed_memory);
      --  End update Mode_Logic_Props/Requirements/NAV_Active_When_Capture_Cond_Met/Changed
   end up;
end NAV_Active_When_Capture_Cond_Met;
--  @EOF
