package body Refined_Depends_Illegal
  with SPARK_Mode
is
   package body No_Abstract_State is
      procedure P1 (Par : out Integer)
        with Refined_Global => (Par => Global_Var)
      is
      begin
         Par := 0;
      end P1;
   end No_Abstract_State;


   package body No_Contract
     with Refined_State => (State => Var)
   is
      Var : Integer;

      procedure No_Depends_Contract (Par : out Integer)
        with Refined_Depends => (Par => Var)
      is
      begin
         Par := Var;
      end No_Depends_Contract;


      procedure Refined_Depends_On_Body_As_Spec (Par : out Integer)
        --  TU: 2. A Refined_Depends aspect is permitted on a body_stub (if one
        --  is present) or subprogram body if and only if it has a declaration
        --  in the specification of an enclosing package and the declaration has
        --  a Depends aspect which denotes a state abstraction declared by the
        --  package and the refinement of the state abstraction is visible.
        with Refined_Depends => (Par => Var)
      is
      begin
         Var := 0;
      end Refined_Depends_On_Body_As_Spec;
   end No_Contract;


   package body Refinement_Is_Visible
     with Refined_State => (State  => (W, X),
                            State2 => (Y, Z),
                            State3 => null)
   is
      W, X, Y, Z : Integer := 1;

      procedure Not_Correctly_Refined
        with Refined_Global  => (Input  => Var,
                                 Output => (W, X)),
             Refined_Depends => (W => Var)  --  Did not mention X
      is
      begin
         W := 2 * Var;
      end Not_Correctly_Refined;


      procedure Not_Correctly_Repeated (Par : out Integer)
        with Refined_Global  => (Input  => (X, Y, Var2),
                                 Output => Var),
             Refined_Depends => (Par => (X, Y))
      is
      begin
         Par := X + Y;
      end Not_Correctly_Repeated;


      procedure Additional_Inputs_And_Outputs
        with Refined_Depends => (Y    => (X, Var),
                                 Var2 => X)
      is
      begin
         Var2 := X;
         Y    := X + Var;
      end Additional_Inputs_And_Outputs;


      procedure Non_Distinct_Entities
        with Refined_Depends => (Var => (W, X, W))
      is
      begin
         Var := W + X;
      end Non_Distinct_Entities;


      procedure Does_Not_Require_Null
        with Refined_Depends => (Var => (Var2, null))
      is
      begin
         Var := Var2;
      end Does_Not_Require_Null;
   end Refinement_Is_Visible;
end Refined_Depends_Illegal;
