package Derived_Types_And_Classes_Illegal
  with SPARK_Mode
is
   type Record_T is tagged record
      A : access Integer;
   end record;

   type Extended_Record_T is new Record_T with record
      --  Not in SPARK since ancestor Record_T is NOT in SPARK. The tools do
      --  not emmit an error message here but this is indirectly picked up
      --  since the ancestor is flagged as BIT in SPARK.
      B : Integer;
   end record;
end Derived_Types_And_Classes_Illegal;
