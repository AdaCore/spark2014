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

package body AP_Engaged_Implies_Modes_On is
   True_out1 : Boolean;
   Unit_Delay_memory : Boolean;

   procedure initStates is
   begin
      --  Block Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On/Unit Delay
      Unit_Delay_memory := True;
      --  End Block Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On/Unit Delay
   end initStates;

   procedure comp (Is_AP_Engaged : Boolean; Modes_On : Boolean) is
      use type Boolean;
      Unit_Delay_out1 : Boolean;
      Is_AP_Engaged_out1 : Boolean;
      Modes_On_out1 : Boolean;
      NOT1_out1 : Boolean;
      NOT5_out1 : Boolean;
      OR_out1 : Boolean;
   begin
      --  Block Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On/Unit Delay
      Unit_Delay_out1 := Unit_Delay_memory;
      --  End Block Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On/Unit Delay

      --  Block Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On/Is_AP_Engaged
      Is_AP_Engaged_out1 := Is_AP_Engaged;
      --  End Block Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On/Is_AP_Engaged

      --  Block Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On/Modes_On
      Modes_On_out1 := Modes_On;
      --  End Block Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On/Modes_On

      --  Block Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On/My_Implies/NOT1
      NOT1_out1 := not  (Is_AP_Engaged_out1);
      --  End Block Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On/My_Implies/NOT1

      --  Block Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On/My_Implies/NOT5
      NOT5_out1 := (NOT1_out1)
         or else (Modes_On_out1);
      --  End Block Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On/My_Implies/NOT5

      --  Block Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On/True
      True_out1 := False;
      --  End Block Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On/True

      --  Block Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On/OR
      OR_out1 := (Unit_Delay_out1)
         or else (NOT5_out1);
      --  End Block Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On/OR

      --  Block Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On/My_Assertion
      pragma Assert (OR_out1, "Violation of assertion at block Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On/My_Assertion");
      --  End Block Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On/My_Assertion
   end comp;

   procedure up is
   begin
      --  update Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On/Unit Delay
      Unit_Delay_memory := True_out1;
      --  End update Mode_Logic_Props/Requirements/AP_Engaged_Implies_Modes_On/Unit Delay
   end up;
end AP_Engaged_Implies_Modes_On;
--  @EOF
