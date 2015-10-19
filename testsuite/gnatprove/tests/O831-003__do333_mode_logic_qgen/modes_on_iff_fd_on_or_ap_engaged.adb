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

package body Modes_On_Iff_FD_On_or_AP_Engaged is
   True_out1 : Boolean;
   Unit_Delay_memory : Boolean;

   procedure initStates is
   begin
      --  Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/Unit Delay
      Unit_Delay_memory := True;
      --  End Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/Unit Delay
   end initStates;

   procedure comp
      (Offside_FD_On : Boolean;
       Is_AP_Engaged : Boolean;
       FD_On : Boolean;
       Modes_On : Boolean)
   is
      use type Boolean;
      Unit_Delay_out1 : Boolean;
      FD_On_out1 : Boolean;
      Is_AP_Engaged_out1 : Boolean;
      Modes_On_out1 : Boolean;
      Offside_FD_On_out1 : Boolean;
      OR1_out1 : Boolean;
      Equals_out1 : Boolean;
      OR_out1 : Boolean;
   begin
      --  Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/Unit Delay
      Unit_Delay_out1 := Unit_Delay_memory;
      --  End Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/Unit Delay

      --  Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/FD_On
      FD_On_out1 := FD_On;
      --  End Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/FD_On

      --  Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/Is_AP_Engaged
      Is_AP_Engaged_out1 := Is_AP_Engaged;
      --  End Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/Is_AP_Engaged

      --  Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/Modes_On
      Modes_On_out1 := Modes_On;
      --  End Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/Modes_On

      --  Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/Offside_FD_On
      Offside_FD_On_out1 := Offside_FD_On;
      --  End Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/Offside_FD_On

      --  Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/OR1
      OR1_out1 := ((Offside_FD_On_out1)
         or else (Is_AP_Engaged_out1))
            or else (FD_On_out1);
      --  End Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/OR1

      --  Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/Equals
      Equals_out1 := (OR1_out1) = (Modes_On_out1);
      --  End Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/Equals

      --  Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/True
      True_out1 := False;
      --  End Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/True

      --  Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/OR
      OR_out1 := (Unit_Delay_out1)
         or else (Equals_out1);
      --  End Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/OR

      --  Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/My_Assertion
      pragma Assert (OR_out1, "Violation of assertion at block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/My_Assertion");
      --  End Block Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/My_Assertion
   end comp;

   procedure up is
   begin
      --  update Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/Unit Delay
      Unit_Delay_memory := True_out1;
      --  End update Mode_Logic_Props/Requirements/Modes_On_Iff_FD_On_or_AP_Engaged/Unit Delay
   end up;
end Modes_On_Iff_FD_On_or_AP_Engaged;
--  @EOF
