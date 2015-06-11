package Refined_Global_Illegal
  with SPARK_Mode
is
   package No_Abstract_State is
      Var : Integer;

      procedure P1
        --  TU: 2. A Refined_Global aspect is permitted on a body_stub
        --  (if one is present), subprogram body, entry body, or task
        --  body if and only if the stub or body is the completion of
        --  a declaration occurring in the specification of an
        --  enclosing package, the declaration has a Global aspect
        --  which denotes a state abstraction declared by the package
        --  and the refinement of the state abstraction is visible.
        with Global => Var;
   end No_Abstract_State;


   package No_Contract
     with Abstract_State => State
   is
      procedure No_Global_Contract;
      --  TU: 2. A Refined_Global aspect is permitted on a body_stub
      --  (if one is present), subprogram body, entry body, or task
      --  body if and only if the stub or body is the completion of a
      --  declaration occurring in the specification of an enclosing
      --  package, the declaration has a Global aspect which denotes a
      --  state abstraction declared by the package and the refinement
      --  of the state abstraction is visible.
   end No_Contract;


   package Refinement_Is_Visible
     with Abstract_State => (State, State2)
   is
      --  TU: 3. A Refined_Global aspect specification shall *refine* the
      --  subprogram's Global aspect as follows:
      --  a. For each ``global_item`` in the Global aspect which denotes a
      --     state abstraction whose non-**null** refinement is visible at
      --     the point of the Refined_Global aspect specification, the
      --     Refined_Global specification shall include one or more
      --     ``global_items`` which denote ``constituents`` of that state
      --     abstraction.
      --  b. For each ``global_item`` in the Global aspect which denotes a
      --     state abstraction whose **null** refinement is visible at the
      --     point of the Refined_Global aspect specification, the
      --     Refined_Global specification shall be omitted, or if required by
      --     the syntax of a ``global_specification`` replaced by a **null**
      --     in the Refined_Global aspect.
      --  c. For each ``global_item`` in the Global aspect which does not
      --     denote a state abstraction whose refinement is visible, the
      --     Refined_Global specification shall include exactly one
      --     ``global_item`` which denotes the same entity as the
      --     ``global_item`` in the Global aspect.
      --  d. No other ``global_items`` shall be included in the Refined_Global
      --     aspect specification.
      procedure Should_Reference_Constituents
        with Global => (Output => State);


      procedure Should_Reference_Constituents_2
        with Global => (Output => State);


      procedure Not_Distinct_Entities
        --  TU: 4. ``Global_items`` in a Refined_Global
        --  ``aspect_specification`` shall denote distinct entities.
        with Global => (Output => State);


      --  TU: 5. The mode of each ``global_item`` in a Refined_Global aspect
      --  shall match that of the corresponding ``global_item`` in the Global
      --  aspect unless that corresponding ``global_item`` denotes a state
      --  abstraction whose refinement is visible. In that case, the modes of
      --  the ``global_items`` in the Refined_Global aspect which denote
      --  (direct or indirect) constituents of that state abstraction
      --  collectively determine (as described below) an "effective mode" for
      --  the abstraction. That "effective mode" shall match that of the
      --  corresponding ``global_item`` in the Global aspect; it is determined
      --  as follows:
      --  a. If every constituent of the abstraction is mentioned in the
      --     Refined_Global aspect with a mode of Output, then the effective
      --     mode is Output;
      --  b. Otherwise, if at least one consistituent of the abstraction is
      --     mentioned in the Refined_Global aspect with a mode of Output or
      --     In_Out, then the effective mode is In_Out;
      --  c. Otherwise, if at least one constituent of the abstraction is
      --     mentioned in the Refined_Global aspect with a mode of Input, then
      --     the effective mode is Input;
      --  d. Otherwise, the effective mode is Proof_In.
      procedure In_Out_Refinement_Without_Input
        with Global => (In_Out => State);


      procedure In_Out_Refinement_Without_Output (Par : out Integer)
        with Global => (In_Out => State);


      procedure Not_All_Constituents_Are_Referenced
        --  TU: 6. If the Global aspect specification references a state
        --  abstraction with a ``mode_selector`` of Output, whose refinement is
        --  visible, then every ``constituent`` of that state abstraction shall
        --  be referenced in the Refined_Global aspect specification.
        with Global => (Output => State2);
   end Refinement_Is_Visible;
end Refined_Global_Illegal;
