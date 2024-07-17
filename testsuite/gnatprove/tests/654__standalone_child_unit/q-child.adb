
function Q.Child return Boolean with SPARK_Mode is
begin
   pragma Assert (False); -- @ASSERT:FAIL
   return True;
end Q.Child;
