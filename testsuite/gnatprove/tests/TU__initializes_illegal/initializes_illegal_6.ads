package Initializes_Illegal_6
  --  TU: 1. For each state abstraction denoted by the ``name`` of an
  --  ``initialization_item`` of an Initializes aspect of a package, all the
  --  ``constituents`` of the state abstraction must be initialized by:
  --  * initialization within the package; or
  --  * assumed pre-initialization (in the case of external states); or
  --  * for constituents which reside in another unit [and have a Part_Of
  --    indicator associated with their declaration (see
  --    :ref:`package_hierarchy`)] by their declaring package. [It follows
  --    that such constituents will appear in the initialization clause
  --    of the declaring unit unless they are external states.]
  with SPARK_Mode,
       Abstract_State => State,
       Initializes    => State
is
   function F1 return Integer
     with Global => State;
end Initializes_Illegal_6;
