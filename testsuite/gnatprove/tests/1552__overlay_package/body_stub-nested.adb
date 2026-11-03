separate (Body_Stub)
package body Nested is
   procedure Touch is null;
begin
   pragma Assert (X = 0); -- ASSERT:FAIL
end Nested;
