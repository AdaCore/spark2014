procedure Arrays with SPARK_Mode is
   package T is
      type A is array (Positive range <>) of Positive;
      function Read return A with
        Import, Global => null, Potentially_Invalid => Read'Result,
        Post => Read'Result'First = 5 and Read'Result'Last = 6
          and not Read'Result'Valid_Scalars;
      function Is_Valid (X : A) return Boolean with
        Import, Global => null, Potentially_Invalid => X,
        Post => Is_Valid'Result = X'Valid_Scalars;
      procedure Fill (X : out A) with
        Import, Global => null, Always_Terminates, Potentially_Invalid => X,
        Post => not X'Valid_Scalars;
      procedure Update (X : in out A) with
        Import, Global => null, Always_Terminates, Potentially_Invalid => X,
        Post => X'Valid_Scalars;
      type D is new A;
   end T;
   package body T is
   end T;
   use T;
   X : D (5 .. 6) := Read with Potentially_Invalid;
begin
   pragma Assert (not X'Valid_Scalars);
   pragma Assert (not Is_Valid (X));
   Fill (X);
   pragma Assert (not X'Valid_Scalars);
   Update (X);
   pragma Assert (X'Valid_Scalars);
   X (5) := 1;
   pragma Assert (X (5)'Valid);
   Fill (X);
   pragma Assert (X'Valid_Scalars); -- @ASSERT:FAIL
end Arrays;
