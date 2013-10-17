package Initializes_Illegal
  with SPARK_Mode
is
   package Illegal_Syntax
     --  TU: ::
     --  initialization_spec ::= initialization_list
     --                        | null
     --  initialization_list ::= initialization_item
     --                     | ( initialization_item { , initialization_item } )
     --  initialization_item ::= name [ => input_list]
     with Initializes    => (null, X)
   is
      X : Integer;
   end Illegal_Syntax;


   package Incorrect_Placement
     --  TU: 1. An Initializes aspect shall only appear in the
     --  ``aspect_specification`` of a ``package_specification``.
     with Abstract_State => S
   is
      procedure Does_Nothing;
   end Incorrect_Placement;
end Initializes_Illegal;
