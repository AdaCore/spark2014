package Initializes_Illegal_4
  with SPARK_Mode
is
   G_Var, G_Var2 : Integer := 20;

   package Pac1
     --  TU: 8. The Initializes aspect of a package specification asserts which
     --  state abstractions and visible variables of the package are
     --  initialized by the elaboration of the package, both its specification
     --  and body, and any units which have state abstractions or variable
     --  declarations that are part (constituents) of a state abstraction
     --  declared by the package.
     --  [A package with a **null** ``initialization_list``, or no Initializes
     --  aspect does not initialize any of its state abstractions or
     --  variables.]
     with Abstract_State => State,
          Initializes    => null
   is
      X : Integer;
   end Pac1;

   package Pac2
     --  TU: 10. If the Initializes aspect is specified for a package, then
     --  after the body (which may be implicit if the package has no explicit
     --  body) has completed its elaboration, every (entire) variable and
     --  state abstraction denoted by a ``name`` in the Initializes aspect
     --  shall be initialized. A state abstraction is said to be
     --  initialized if all of its constituents are initialized. An entire
     --  variable is initialized if all of its components are initialized.
     --  Other parts of the visible state of the package shall not be
     --  initialized.
     with Abstract_State => (State, State2),
          Initializes    => (State, Var)
   is
      Var, Var2 : Integer := 0;  --  Var should not be initialized
   end Pac2;

   package Pac3
     --  TU: 11. If an ``initialization_item`` has an ``input_list`` then the
     --  variables and state abstractions denoted in the input list shall
     --  be used in determining the initialized value of the entity denoted
     --  by the ``name`` of the ``initialization_item``.

     --  TU: 12. All variables and state abstractions which are not declared
     --  within the package but are used in the initialization of an
     --  ``initialization_item`` shall appear in an ``input_list`` of the
     --  ``initialization_item``.
     with Abstract_State => State,
          Initializes    => (Var   => G_Var,
                             State => G_Var)
   is
      Var : Integer := G_Var + G_Var2;  --  Var should only depend on G_Var
                                        --  for its initialization
   end Pac3;

   package Pac4
     --  TU: 6. An ``initialization_item`` with a **null** ``input_list`` is
     --  equivalent to the same ``initialization_item`` without an
     --  ``input_list``.
     --  [That is Initializes => (A => **null**) is equivalent to
     --  Initializes => A.]
     with Initializes => A
   is
      A : Integer := G_Var;  --  A should be initialized from null (not G_Var).
   end Pac4;
end Initializes_Illegal_4;
