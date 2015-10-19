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

package body Onside_FD_Implies_Modes_On is

   procedure comp (FD_On : Boolean; Modes_On : Boolean) is
      use type Boolean;
      FD_On_out1 : Boolean;
      Modes_On_out1 : Boolean;
      NOT1_out1 : Boolean;
      NOT5_out1 : Boolean;
   begin
      --  Block Mode_Logic_Props/Requirements/Onside_FD_Implies_Modes_On/FD_On
      FD_On_out1 := FD_On;
      --  End Block Mode_Logic_Props/Requirements/Onside_FD_Implies_Modes_On/FD_On

      --  Block Mode_Logic_Props/Requirements/Onside_FD_Implies_Modes_On/Modes_On
      Modes_On_out1 := Modes_On;
      --  End Block Mode_Logic_Props/Requirements/Onside_FD_Implies_Modes_On/Modes_On

      --  Block Mode_Logic_Props/Requirements/Onside_FD_Implies_Modes_On/My_Implies/NOT1
      NOT1_out1 := not  (FD_On_out1);
      --  End Block Mode_Logic_Props/Requirements/Onside_FD_Implies_Modes_On/My_Implies/NOT1

      --  Block Mode_Logic_Props/Requirements/Onside_FD_Implies_Modes_On/My_Implies/NOT5
      NOT5_out1 := (NOT1_out1)
         or else (Modes_On_out1);
      --  End Block Mode_Logic_Props/Requirements/Onside_FD_Implies_Modes_On/My_Implies/NOT5

      --  Block Mode_Logic_Props/Requirements/Onside_FD_Implies_Modes_On/My_Assertion
      pragma Assert (NOT5_out1, "Violation of assertion at block Mode_Logic_Props/Requirements/Onside_FD_Implies_Modes_On/My_Assertion");
      --  End Block Mode_Logic_Props/Requirements/Onside_FD_Implies_Modes_On/My_Assertion
   end comp;
end Onside_FD_Implies_Modes_On;
--  @EOF
