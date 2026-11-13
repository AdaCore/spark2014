procedure Constrained with SPARK_Mode is
   package T is
      type A is array (Positive range <>) of Positive;
      type R (Length : Positive) is record
         Items : A (1 .. Length);
      end record;
      function Read return R with
        Import, Global => null, Potentially_Invalid => Read'Result,
        Post => Read'Result.Length = 2
          and not Read'Result'Valid_Scalars;
      function Is_Valid (X : R) return Boolean with
        Import, Global => null, Potentially_Invalid => X,
        Post => Is_Valid'Result = X'Valid_Scalars;
      procedure Update (X : in out R) with
        Import, Global => null, Always_Terminates, Potentially_Invalid => X,
        Post => X'Valid_Scalars;
      type D is new R (2);
   end T;
   package body T is
   end T;
   use T;
   X : D := Read with Potentially_Invalid;
begin
   pragma Assert (not X'Valid_Scalars);
   pragma Assert (not Is_Valid (X));
   Update (X);
   pragma Assert (X'Valid_Scalars);
   X.Items (1) := 1;
   pragma Assert (X.Items (1)'Valid);
end Constrained;
