with Parent_Types; use Parent_Types;

procedure Test with SPARK_Mode is
   function Read return Leaf with
     Import, Global => null, Potentially_Invalid => Read'Result,
     Post => not Read'Result'Valid_Scalars;
   X : Leaf := Read with Potentially_Invalid;
begin
   pragma Assert (not X'Valid_Scalars);
   pragma Assert (X'Valid_Scalars); -- @ASSERT:FAIL
end Test;
