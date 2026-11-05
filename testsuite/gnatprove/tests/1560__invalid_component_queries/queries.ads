package Queries with SPARK_Mode is
   type R is record
      F, G : Positive;
   end record;

   type R_Array is array (Positive range <>) of R;

   type Nested is record
      Item : R;
      Items : R_Array (1 .. 2);
   end record;

   procedure Field_Query (X : out R) with
     Import, Global => null, Always_Terminates, Potentially_Invalid => X,
     Post => X.F'Valid;

   function Make return R with
     Import, Global => null, Potentially_Invalid => Make'Result,
     Post => Make'Result.F'Valid;

   procedure Nested_Query (X : out Nested) with
     Import, Global => null, Always_Terminates, Potentially_Invalid => X,
     Post => X.Item.F'Valid and X.Item'Valid_Scalars;

   procedure Array_Query (X : out Nested; I : Positive) with
     Import, Global => null, Always_Terminates, Potentially_Invalid => X,
     Pre => I in 1 .. 2,
     Post => X.Items (I).F'Valid and X.Items (1 .. I)'Valid_Scalars;

   procedure Old_Query (X : in out Nested) with
     Import, Global => null, Always_Terminates, Potentially_Invalid => X,
     Post => X'Old.Item.F'Valid and X.Item'Old.F'Valid;

   --  Component guards are still outside the heuristic

   procedure Guarded_Read (X : out R) with
     Import, Global => null, Always_Terminates, Potentially_Invalid => X,
     Post => X.F'Valid and then X.F = 1;

   --  These contexts still read potentially invalid values

   procedure Unguarded_Read (X : out R) with
     Import, Global => null, Always_Terminates, Potentially_Invalid => X,
     Post => X.F = 1;

   procedure Scalar_Old_Query (X : in out R) with
     Import, Global => null, Always_Terminates, Potentially_Invalid => X,
     Post => X.F'Old'Valid; -- @VALIDITY_CHECK:FAIL

   procedure Index_Query (X : out R_Array; I : in out R) with
     Import, Global => null, Always_Terminates,
     Potentially_Invalid => (X, I),
     Post => X (I.F).F'Valid;

   procedure Bound_Query (X : out R_Array; I : in out R) with
     Import, Global => null, Always_Terminates,
     Potentially_Invalid => (X, I),
     Post => X (1 .. I.F)'Valid_Scalars;
end Queries;
