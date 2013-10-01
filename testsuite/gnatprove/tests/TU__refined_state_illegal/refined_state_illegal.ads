package Refined_State_Illegal
  with SPARK_Mode
is
   package Pac1
     --  TU: ::
     --    refinement_list   ::= refinement_clause
     --                        | ( refinement_clause { , refinement_clause } )
     --    refinement_clause ::= state_name => constituent_list
     --    constituent_list  ::= null
     --                        | constituent
     --                        | ( constituent { , constituent } )
     --  where
     --    ``constituent ::=`` *object_*\ ``name | state_name``
     with Abstract_State => S
   is
      procedure P1;
   end Pac1;


   package Pac2
     --  TU: 2. A Refined_State aspect shall only appear in the
     --  ``aspect_specification`` of a ``package_body``. [The use of
     --  ``package_body`` rather than package body allows this aspect to be
     --  specified for generic package bodies.]
     with Refined_State => (S => null)
   is

   end Pac2;


   package Pac3
     --  TU: 3. If a ``package_specification`` has a non-null Abstract_State
     --  aspect its body shall have a Refined_State aspect.
     with Abstract_State => S
   is
      function F1 return Boolean;
   end Pac3;


   package Pac4 is
     --  TU: 4. If a ``package_specification`` does not have an Abstract_State
     --  aspect, then the corresponding ``package_body`` shall not have a
     --  Refined_State aspect.
      procedure P1;
   end Pac4;


   package Pac5
     --  TU: 5. Each ``constituent`` shall be either a variable or a state
     --  abstraction.
     with Abstract_State => S
   is
      function F1 return Boolean;
   end Pac5;


   package Pac6
     --  TU: 6. An object which is a ``constituent`` shall be an entire object.
     with Abstract_State => S
   is
      type Record_T is
         record
            A, B : Natural;
         end record;

      procedure P1;
   end Pac6;


   package Pac7
     --  TU: 8. Each *abstract_*\ ``state_name`` declared in the package
     --  specification shall be denoted exactly once as the ``state_name``
     --  of a ``refinement_clause`` in the Refined_State aspect of the body
     --  of the package.
     with Abstract_State => (S1, S2)
   is
      procedure P1;
   end Pac7;


   package Pac8
     --  TU: 7. A ``constituent`` of a state abstraction of a package shall
     --  denote either an entity with no Part_Of ``option`` or aspect which is
     --  part of the hidden state of the package, or an entity whose
     --  declaration has a Part_Of ``option`` or aspect which denotes this
     --  state abstraction (see :ref:`package_hierarchy`).

     --  TU: 9. Every entity of the hidden state of a package shall be denoted
     --  as a ``constituent`` of exactly one *abstract_*\ ``state_name`` in the
     --  Refined_State aspect of the package and shall not be denoted more than
     --  once.
     --  [These ``constituents`` are either variables declared in the private
     --  part or body of the package, or the declarations from the visible part
     --  of nested packages declared immediately therein.]
     with Abstract_State => (S1, S2)
   is
      procedure P1;
   private
      Pr_Var1 : Natural;
      Pr_Var2 : Boolean;
   end Pac8;


   package Pac9
     --  TU: 13. A **null** ``constituent_list`` indicates that the named
     --  abstract state has no constituents and termed a *null_refinement*.
     --  The state abstraction does not represent any actual state at
     --  all. [This feature may be useful to minimize changes to Global and
     --  Depends aspects if it is believed that a package may have some
     --  extra state in the future, or if hidden state is removed.]
     with Abstract_State => S
   is
      function F1 return Integer
        with Global => S;
   end Pac9;


   package Pac10
     --  TU: 12. A Refined_State aspect of a ``package_body`` completes the
     --  declaration of the state abstractions occurring in the
     --  corresponding ``package_specification`` and defines the objects
     --  and each subordinate state abstraction that are the
     --  ``constituents`` of the *abstract_*\ ``state_names`` declared in
     --  the ``package_specification``.
     with Abstract_State => (S1, S2)
   is
      procedure P1;
   end Pac10;
end Refined_State_Illegal;
