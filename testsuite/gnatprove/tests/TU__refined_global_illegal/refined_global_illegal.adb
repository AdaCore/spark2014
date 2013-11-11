package body Refined_Global_Illegal
  with SPARK_Mode
is
   package body No_Abstract_State is
      procedure P1
        with Refined_Global => (Output => Var)
      is
      begin
         Var := 0;
      end P1;
   end No_Abstract_State;


   package body No_Contract
     with Refined_State => (State => Var)
   is
      Var : Integer;

      procedure No_Global_Contract
        with Refined_Global => (Output => Var)
      is
      begin
         Var := 0;
      end No_Global_Contract;


      procedure Refined_Global_On_Body_As_Spec
        --  TU: 2. A Refined_Global aspect is permitted on a body_stub (if one
        --  is present) or subprogram body if and only if it has a declaration
        --  in the specification of an enclosing package, the declaration has a
        --  Global aspect which denotes a state abstraction declared by the
        --  package and the refinement of the state abstraction is visible.
        with Refined_Global => (Output => Var)
      is
      begin
         Var := 0;
      end Refined_Global_On_Body_As_Spec;
   end No_Contract;


   package body Refinement_Is_Visible
     with Refined_State => (State  => X,
                            State2 => (Y, Z))
   is
      X, Y, Z : Integer;


      procedure Should_Reference_Constituents
        with Refined_Global => (Output => State)
      is
      begin
         X := 0;
      end Should_Reference_Constituents;


      procedure Should_Reference_Constituents_2
        with Refined_Global => (Output => (X, Y))
      is
      begin
         X := 0;
      end Should_Reference_Constituents_2;


      procedure Not_Distinct_Entities
        with Refined_Global => (Output => (X, X))
      is
      begin
         X := 0;
      end Not_Distinct_Entities;


      procedure In_Out_Refinement_Without_Input
        with Refined_Global => (Output => X)
      is
      begin
         X := 0;
      end In_Out_Refinement_Without_Input;


      procedure In_Out_Refinement_Without_Output (Par : out Integer)
        with Refined_Global => (Input => X)
      is
      begin
         Par := X;
      end In_Out_Refinement_Without_Output;


      procedure Not_All_Constituents_Are_Referenced
        with Refined_Global => (Output => Y)
      is
      begin
         Y := 0;
      end Not_All_Constituents_Are_Referenced;
   end Refinement_Is_Visible;
end Refined_Global_Illegal;
