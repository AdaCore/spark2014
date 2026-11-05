procedure Matrix with SPARK_Mode is
   package T is
      type Index is mod 256 with Size => 8;
      type R is record
         F : Positive;
      end record;
      type A is array (Index range 1 .. 2, Boolean) of R;
      function Read return A with
        Import, Global => null, Potentially_Invalid => Read'Result,
        Post => not Read'Result'Valid_Scalars;
      function Is_Valid (X : A) return Boolean with
        Import, Global => null, Potentially_Invalid => X,
        Post => Is_Valid'Result = X'Valid_Scalars;
      type D is new A;
   end T;
   package body T is
   end T;
   use T;
   X : D := Read with Potentially_Invalid;
begin
   pragma Assert (not X'Valid_Scalars);
   pragma Assert (not Is_Valid (X));
   X (1, False).F := 1;
   pragma Assert (X (1, False).F'Valid);
   pragma Assert (X'Valid_Scalars); -- @ASSERT:FAIL
end Matrix;
