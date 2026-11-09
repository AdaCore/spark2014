procedure Records with SPARK_Mode is
   package T is
      type R is record
         F : Positive;
      end record;
      function Read return R with
        Import, Global => null, Potentially_Invalid => Read'Result,
        Post => not Read'Result'Valid_Scalars;
      function Is_Valid (X : R) return Boolean with
        Import, Global => null, Potentially_Invalid => X,
        Post => Is_Valid'Result = X'Valid_Scalars;
      procedure Fill (X : out R) with
        Import, Global => null, Always_Terminates, Potentially_Invalid => X,
        Post => not X'Valid_Scalars;
      procedure Update (X : in out R) with
        Import, Global => null, Always_Terminates, Potentially_Invalid => X,
        Post => X'Valid_Scalars;
      type D is new R;
      type DD is new D;
   end T;
   package body T is
   end T;
   use T;
   X : DD := Read with Potentially_Invalid;
begin
   pragma Assert (not X'Valid_Scalars);
   pragma Assert (not Is_Valid (X));
   Fill (X);
   pragma Assert (not X'Valid_Scalars);
   Update (X);
   pragma Assert (X'Valid_Scalars);
   X.F := 1;
   pragma Assert (X.F'Valid);
   Fill (X);
   pragma Assert (X'Valid_Scalars); -- @ASSERT:FAIL
end Records;
