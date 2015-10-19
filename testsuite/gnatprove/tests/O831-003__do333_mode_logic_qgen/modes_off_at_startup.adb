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

package body Modes_Off_At_Startup is
   True_out1 : Boolean;
   Unit_Delay_memory : Boolean;

   procedure initStates is
   begin
      --  Block Mode_Logic_Props/Requirements/Modes_Off_At_Startup/Unit Delay
      Unit_Delay_memory := False;
      --  End Block Mode_Logic_Props/Requirements/Modes_Off_At_Startup/Unit Delay
   end initStates;

   procedure comp (Modes_On : Boolean) is
      use type Boolean;
      Unit_Delay_out1 : Boolean;
      Modes_On_out1 : Boolean;
      NOT_out1 : Boolean;
      OR_out1 : Boolean;
   begin
      --  Block Mode_Logic_Props/Requirements/Modes_Off_At_Startup/Unit Delay
      Unit_Delay_out1 := Unit_Delay_memory;
      --  End Block Mode_Logic_Props/Requirements/Modes_Off_At_Startup/Unit Delay

      --  Block Mode_Logic_Props/Requirements/Modes_Off_At_Startup/Modes_On
      Modes_On_out1 := Modes_On;
      --  End Block Mode_Logic_Props/Requirements/Modes_Off_At_Startup/Modes_On

      --  Block Mode_Logic_Props/Requirements/Modes_Off_At_Startup/NOT
      NOT_out1 := not  (Modes_On_out1);
      --  End Block Mode_Logic_Props/Requirements/Modes_Off_At_Startup/NOT

      --  Block Mode_Logic_Props/Requirements/Modes_Off_At_Startup/True
      True_out1 := True;
      --  End Block Mode_Logic_Props/Requirements/Modes_Off_At_Startup/True

      --  Block Mode_Logic_Props/Requirements/Modes_Off_At_Startup/OR
      OR_out1 := (Unit_Delay_out1)
         or else (NOT_out1);
      --  End Block Mode_Logic_Props/Requirements/Modes_Off_At_Startup/OR

      --  Block Mode_Logic_Props/Requirements/Modes_Off_At_Startup/My_Assertion
      pragma Assert (OR_out1, "Violation of assertion at block Mode_Logic_Props/Requirements/Modes_Off_At_Startup/My_Assertion");
      --  End Block Mode_Logic_Props/Requirements/Modes_Off_At_Startup/My_Assertion
   end comp;

   procedure up is
   begin
      --  update Mode_Logic_Props/Requirements/Modes_Off_At_Startup/Unit Delay
      Unit_Delay_memory := True_out1;
      --  End update Mode_Logic_Props/Requirements/Modes_Off_At_Startup/Unit Delay
   end up;
end Modes_Off_At_Startup;
--  @EOF
