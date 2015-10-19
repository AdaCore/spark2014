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

package body No_Higher is

   procedure comp
      (No_Higher_Above : Boolean;
       Input : Boolean;
       No_Higher : out Boolean;
       No_Higher_Below : out Boolean)
   is
      use type Boolean;
      Input_out1 : Boolean;
      No_Higher_Above_out1 : Boolean;
      Not_out1 : Boolean;
      AND_out1 : Boolean;
   begin
      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_ALTSEL_Capture/Input
      Input_out1 := Input;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_ALTSEL_Capture/Input

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_ALTSEL_Capture/No_Higher_Above
      No_Higher_Above_out1 := No_Higher_Above;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_ALTSEL_Capture/No_Higher_Above

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_ALTSEL_Capture/No_Higher
      No_Higher := No_Higher_Above_out1;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_ALTSEL_Capture/No_Higher

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_ALTSEL_Capture/Not
      Not_out1 := not  (Input_out1);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_ALTSEL_Capture/Not

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_ALTSEL_Capture/AND
      AND_out1 := (No_Higher_Above_out1)
         and then (Not_out1);
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_ALTSEL_Capture/AND

      --  Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_ALTSEL_Capture/No_Higher_Below
      No_Higher_Below := AND_out1;
      --  End Block Mode_Logic_Props/Requirements/No_Higher_Event/No_Higher_ALTSEL_Capture/No_Higher_Below
   end comp;
end No_Higher;
--  @EOF
