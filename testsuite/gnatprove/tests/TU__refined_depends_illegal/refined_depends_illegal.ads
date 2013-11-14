package Refined_Depends_Illegal
  with SPARK_Mode
is
   package No_Abstract_State is
      Global_Var : Integer;

      procedure P1 (Par : out Integer)
        --  TU: 2. A Refined_Depends aspect is permitted on a body_stub (if one
        --  is present) or subprogram body if and only if it has a declaration
        --  in the specification of an enclosing package and the declaration has
        --  a Depends aspect which denotes a state abstraction declared by the
        --  package and the refinement of the state abstraction is visible.
        with Global  => Global_Var,
             Depends => (Par => Global_Var);
   end No_Abstract_State;


   package No_Contract
     with Abstract_State => State
   is
     procedure No_Depends_Contract (Par : out Integer);
     --  TU: 2. A Refined_Depends aspect is permitted on a body_stub (if one
     --  is present) or subprogram body if and only if it has a declaration
     --  in the specification of an enclosing package and the declaration has
     --  a Depends aspect which denotes a state abstraction declared by the
     --  package and the refinement of the state abstraction is visible.
   end No_Contract;


   package Refinement_Is_Visible
     with Abstract_State => (State, State2, State3),
          Initializes    => (Var, Var2)
   is
      Var, Var2 : Integer := 1;

      --  TU: 3. A Refined_Depends aspect specification is, in effect, a copy
      --  of the corresponding Depends aspect specification except that any
      --  references in the Depends aspect to a state abstraction, whose
      --  refinement is visible at the point of the Refined_Depends
      --  specification, are replaced with references to zero or more direct
      --  or indirect constituents of that state abstraction. A
      --  Refined_Depends aspect shall have a ``dependency_relation`` which
      --  is derivable from the original given in the Depends aspect as
      --  follows:
      --  a. A *partially refined dependency relation* is created by first
      --     copying, from the Depends aspect, each ``output`` that is not
      --     state abstraction whose refinement is visible at the point of
      --     the Refined_Depends aspect, along with its ``input_list``, to
      --     the partially refined dependency relation as an ``output``
      --     denoting the same entity with an ``input_list`` denoting the
      --     same entities as the original. [The order of the ``outputs`` and
      --     the order of ``inputs`` within the ``input_list`` is
      --     insignificant.]
      --  b. The partially refined dependency relation is then extended by
      --     replacing each ``output`` in the Depends aspect that is a state
      --     abstraction, whose refinement is visible at the point of the
      --     Refined_Depends, by zero or more ``outputs`` in the partially
      --     refined dependency relation. It shall be zero only for a
      --     **null** refinement, otherwise all of the ``outputs`` shall
      --     denote a ``constituent`` of the state abstraction.
      --  c. If the ``output`` in the Depends_Aspect denotes a state
      --     abstraction which is not also an ``input``, then each
      --     ``constituent`` of the state abstraction shall be denoted as an
      --     ``output`` of the partially refined dependency relation.
      --  d. These rules may, for each ``output`` in the Depends aspect,
      --     introduce more than one ``output`` in the partially refined
      --     dependency relation. Each of these ``outputs`` has an
      --     ``input_list`` that has zero or more of the ``inputs`` from the
      --     ``input_list`` of the original ``output``.  The union of these
      --     ``inputs`` and the original state abstraction, if it is an
      --     ``input`` in the ``input_list``, shall denote the same ``inputs``
      --     that appear in the ``input_list`` of the original ``output``.
      --  e. If the Depends aspect has a ``null_dependency_clause``, then the
      --     partially refined dependency relation has a
      --     ``null_dependency_clause`` added with an ``input_list`` denoting
      --     the same ``inputs`` as the original.
      --  f. The partially refined dependency relation is completed by
      --     replacing each ``input`` which is a state abstraction, whose
      --     refinement is visible at the point of the Refined_Depends
      --     aspect, by zero or more ``inputs`` which are its
      --     constituents.
      --  g. If a state abstraction is denoted in an ``input_list`` of a
      --     ``dependency_clause`` of the original Depends aspect and its
      --     refinement is visible at the point of the Refined_Depends aspect
      --     (derived via the process described in the rules 3a - 3f above),
      --     then:
      --     - at least one of its ``constituents`` shall be denoted as an
      --       ``input`` in at least one of the ``dependency_clauses`` of the
      --       Refined_Depends aspect corresponding to the original
      --       ``dependency_clause`` in the Depends aspect; or
      --     - at least one of its ``constituents`` shall be denoted in the
      --       ``input_list`` of a ``null_dependency_clause``; or
      --     - the state abstraction is both an ``input`` and an ``output``
      --       and not every ``constituent`` the state abstraction is an
      --       ``output`` of the Refined_Depends aspect. [This rule does not
      --       exclude denoting a ``constituent`` of such a state abstraction
      --       in an ``input_list``.]
      procedure Not_Correctly_Refined
        with Global  => (Input  => Var,
                         Output => State),
             Depends => (State => Var);


      procedure Not_Correctly_Repeated (Par : out Integer)
        with Global  => (Input  => (State, State2, Var2),
                         Output => Var),
             Depends => (Par => (State, State2),
                         Var => Var2);

      --  TU: 5. No other ``outputs`` or ``inputs`` shall be included in the
      --  Refined_Depends aspect specification. ``Outputs`` in the
      --  Refined_Depends aspect specification shall denote distinct
      --  entities. ``Inputs`` in an ``input_list`` shall denote distinct
      --  entities.
      procedure Additional_Inputs_And_Outputs
        with Depends => (State2 => State);


      procedure Non_Distinct_Entities
        with Depends => (Var => State);


      procedure Does_Not_Require_Null
        --  TU: 4. These rules result in omitting each state abstraction whose
        --  **null** refinement is visible at the point of the Refined_Depends.
        --  If and only if required by the syntax, the state abstraction shall
        --  be replaced by a **null** symbol rather than being omitted.
        with Depends => (Var => (State3, Var2));
   end Refinement_Is_Visible;
end Refined_Depends_Illegal;
