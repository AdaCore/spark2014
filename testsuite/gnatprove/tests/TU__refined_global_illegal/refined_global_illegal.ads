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
        --  and either the refinement of the state abstraction is visible
        --  or a Part_Of specification specifying a constituent of the state
        --  abstraction is visible.
        with Global => Var;
   end No_Abstract_State;


   package No_Contract
     with Abstract_State => State
   is
      procedure No_Global_Contract;
      --  TU: 2. A Refined_Global aspect is permitted on a body_stub
      --  (if one is present), subprogram body, entry body, or task
      --  body if and only if the stub or body is the completion of
      --  a declaration occurring in the specification of an
      --  enclosing package, the declaration has a Global aspect
      --  which denotes a state abstraction declared by the package
      --  and either the refinement of the state abstraction is visible
      --  or a Part_Of specification specifying a constituent of the state
      --  abstraction is visible.
   end No_Contract;


   package Refinement_Is_Visible
     with Abstract_State => (State, State2)
   is
      --  TU: 3. A Refined_Global aspect specification shall *refine* the
      --  subprogram's Global aspect as follows:
      --
      --  a. For each ``global_item`` in the Global aspect which denotes a
      --     state abstraction whose non-**null** refinement is visible at the
      --     point of the Refined_Global aspect specification, the
      --     Refined_Global specification shall include one or more
      --     ``global_items`` which denote ``constituents`` of that state
      --     abstraction.
      --
      --  b. For each ``global_item`` in the Global aspect which denotes a
      --     state abstraction whose **null** refinement is visible at the
      --     point of the Refined_Global aspect specification, there are no
      --     corresponding ``global_items`` in the Refined_Global
      --     specification. If this results in a Refined_Global specification
      --     with no ``global_items``, then the Refined_Global specification
      --     shall include a ``null_global_specification``.
      --
      --  c. For each ``global_item`` in the Global aspect which does not
      --     denote a state abstraction whose refinement is visible and does
      --     not denote an optionally refinable state abstraction, the
      --     Refined_Global specification shall include exactly one
      --     ``global_item`` which denotes the same entity as the
      --     ``global_item`` in the Global aspect.
      --
      --  d. For each ``global_item`` in the Global aspect which designates a
      --     state abstraction which is optionally refinable, refinement of the
      --     abstraction is optional in the following sense: either the
      --     reference to the state abstraction may be replaced with references
      --     to its constituents (following the rules of case 'a' above) or not
      --     (in which case the rules of case 'c' above apply). However, only
      --     the latter option is available if the mode of the state
      --     abstraction in the Global specification is Output.
      --
      --  e. No other ``global_items`` shall be included in the Refined_Global
      --     aspect specification.
      --
      --  f. At least one state abstraction mentioned in the Global aspect
      --     aspect specification shall be unmentioned in the Refined_Global
      --     aspect specification. [This usually follows as a consequence of
      --     other rules, but not in some cases involving optionally refinable
      --     state abstractions where the option is declined.]
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
      --  abstraction which is not mentioned in the Refined_Global aspect. In
      --  that case, the modes of the ``global_items`` in the Refined_Global
      --  aspect which denote (direct or indirect) constituents of that state
      --  abstraction collectively determine (as described below) an "effective
      --  mode" for the abstraction. If there is at least one such constituent,
      --  then that "effective mode" shall match that of the corresponding
      --  ``global_item`` in the Global aspect; it is determined as follows:
      --
      --  a. If the refinement of the abstraction is visible and every
      --     constituent of the abstraction is mentioned in the Refined_Global
      --     aspect with a mode of Output, then the effective mode is Output;
      --
      --  b. Otherwise, if at least one constituent of the abstraction is
      --     mentioned in the Refined_Global aspect with a mode of Output or
      --     In_Out, then the effective mode is In_Out;
      --
      --  c. Otherwise, if at least one constituent of the abstraction is
      --     mentioned in the Refined_Global aspect with a mode of Input, then
      --     the effective mode is Input;
      --
      --  d. Otherwise, the effective mode is Proof_In.
      --
      --  [If there is no such consituent (e.g., because a *null* refinement is
      --  visible) then the mode of the state abstraction in the Global aspect
      --  plays no role in determining the legality of the Refined_Global
      --  aspect.]
      procedure In_Out_Refinement_Without_Input
        with Global => (In_Out => State);


      procedure In_Out_Refinement_Without_Output (Par : out Integer)
        with Global => (In_Out => State);


      procedure Not_All_Constituents_Are_Referenced
        with Global => (Output => State2);
   end Refinement_Is_Visible;
end Refined_Global_Illegal;
