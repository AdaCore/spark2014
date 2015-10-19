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

package body Rising_Edge is

   procedure initStates (State : in out Rising_Edge_State) is
      use type Boolean;
      use type Rising_Edge_State;
   begin
      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALT/Unit Delay
      State.Unit_Delay_memory := False;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALT/Unit Delay
   end initStates;

   procedure comp
      (In1 : Boolean;
       Out1 : out Boolean;
       State : in out Rising_Edge_State)
   is
      use type Boolean;
      use type Rising_Edge_State;
      Unit_Delay_out1 : Boolean;
      Logical_Operator2_out1 : Boolean;
      Logical_Operator1_out1 : Boolean;
   begin
      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALT/Unit Delay
      Unit_Delay_out1 := State.Unit_Delay_memory;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALT/Unit Delay

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALT/In1
      State.In1_out1 := In1;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALT/In1

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALT/Logical\nOperator2
      Logical_Operator2_out1 := not  (Unit_Delay_out1);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALT/Logical\nOperator2

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALT/Logical\nOperator1
      Logical_Operator1_out1 := (Logical_Operator2_out1)
         and then (State.In1_out1);
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALT/Logical\nOperator1

      --  Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALT/Out1
      Out1 := Logical_Operator1_out1;
      --  End Block Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALT/Out1
   end comp;

   procedure up (State : in out Rising_Edge_State) is
      use type Boolean;
      use type Rising_Edge_State;
   begin
      --  update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALT/Unit Delay
      State.Unit_Delay_memory := State.In1_out1;
      --  End update Mode_Logic_Props/Mode_Logic/Event_Processing/Rising Edge ALT/Unit Delay
   end up;
end Rising_Edge;
--  @EOF
