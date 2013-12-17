package Derived_Types_And_Classes_Illegal
  with SPARK_Mode
is
   --  TU: 1. An entity declared by a ``derived_type`` declaration is in
   --  |SPARK| if its parent type is in |SPARK|, and if the declaration
   --  contains an ``interface_list`` or a ``record_part`` these must also
   --  contain entities that are in |SPARK|.

   type Record_T is tagged record  --  Not in SPARK
      A : access Integer;
   end record;

   type Extended_Record_T is new Record_T with record
      --  Not in SPARK since ancestor Record_T is NOT in SPARK. The tools do
      --  not emmit an error message here but this is indirectly be picked up
      --  since the ancestor is flagged as not in SPARK.
      B : Integer;
   end record;

   type Bla is interface;  --  An interface type is an abstract tagged type
                           --  that provides a restricted form of multiple
                           --  inheritance. Since tagged types are currently
                           --  NOT in SPARK, neither are interfaces.

   type Bla_Bla is interface and Bla;  --  Also not in SPARK
end Derived_Types_And_Classes_Illegal;
