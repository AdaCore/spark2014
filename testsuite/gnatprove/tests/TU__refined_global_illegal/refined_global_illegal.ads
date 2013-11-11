package Refined_Global_Illegal
  with SPARK_Mode
is
   package No_Abstract_State is
      Var : Integer;

      procedure P1
        --  TU: 2. A Refined_Global aspect is permitted on a body_stub (if one
        --  is present) or subprogram body if and only if it has a declaration
        --  in the specification of an enclosing package, the declaration has a
        --  Global aspect which denotes a state abstraction declared by the
        --  package and the refinement of the state abstraction is visible.
        with Global => Var;
   end No_Abstract_State;


   package No_Contract
     with Abstract_State => State
   is
      procedure No_Global_Contract;
      --  TU: 2. A Refined_Global aspect is permitted on a body_stub (if one
      --  is present) or subprogram body if and only if it has a declaration
      --  in the specification of an enclosing package, the declaration has a
      --  Global aspect which denotes a state abstraction declared by the
      --  package and the refinement of the state abstraction is visible.
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
      --  aspect unless: the ``mode_selector`` specified in the Global aspect
      --  is In_Out; the corresponding ``global_item`` of Global aspect shall
      --  denote a state abstraction whose refinement is visible; and the
      --  ``global_item`` in the Refined_Global aspect is a ``constituent``
      --  of the state abstraction.
      --  a. For this special case when the ``mode_selector`` is In_Out, the
      --     Refined_Global aspect may denote individual ``constituents`` of
      --     the state abstraction as Input, Output, or In_Out (given that
      --     the constituent itself may have any of these ``mode_selectors``)
      --     so long as one or more of the following conditions are
      --     satisfied:
      --     * at least one of the ``constituents`` has a ``mode_selector``
      --       of In_Out; or
      --     * there is at least one of each of a ``constituent`` with a
      --       ``mode_selector`` of Input and of Output; or
      --     * the Refined_Global aspect does not denote all of the
      --       ``constituents`` of the state abstraction but denotes at least
      --       one ``constituent`` that has a ``mode_selector`` of Output.
      --  [This rule ensures that a state abstraction with the
      --  ``mode_selector`` In_Out cannot be refined onto a set of
      --  ``constituents`` that are Output or Input only. The last condition
      --  satisfies this requirement because not all of the ``constituents``
      --  are updated, some are preserved, that is the state abstraction has
      --  a self-dependency.]
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
