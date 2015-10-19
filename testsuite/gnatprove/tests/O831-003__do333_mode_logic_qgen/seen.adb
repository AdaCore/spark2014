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

package body Seen is

   procedure comp
      (Inhibit_In : Boolean;
       Input : Boolean;
       Seen : out Boolean;
       Inhibit_Out : out Boolean)
   is
      use type Boolean;
      Inhibit_In_out1 : Boolean;
      Input_out1 : Boolean;
      Not_out1 : Boolean;
      AND_out1 : Boolean;
      OR_out1 : Boolean;
   begin
      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Capture_Cond_Met_Seen/Inhibit_In
      Inhibit_In_out1 := Inhibit_In;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Capture_Cond_Met_Seen/Inhibit_In

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Capture_Cond_Met_Seen/Input
      Input_out1 := Input;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Capture_Cond_Met_Seen/Input

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Capture_Cond_Met_Seen/Not
      Not_out1 := not  (Inhibit_In_out1);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Capture_Cond_Met_Seen/Not

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Capture_Cond_Met_Seen/AND
      AND_out1 := (Not_out1)
         and then (Input_out1);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Capture_Cond_Met_Seen/AND

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Capture_Cond_Met_Seen/OR
      OR_out1 := (Inhibit_In_out1)
         or else (AND_out1);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Capture_Cond_Met_Seen/OR

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Capture_Cond_Met_Seen/Inhibit_Out
      Inhibit_Out := OR_out1;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Capture_Cond_Met_Seen/Inhibit_Out

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Capture_Cond_Met_Seen/Seen
      Seen := AND_out1;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/ALTSEL_Capture_Cond_Met_Seen/Seen
   end comp;
end Seen;
--  @EOF
