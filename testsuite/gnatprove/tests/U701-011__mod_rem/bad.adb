procedure Bad is
    X : Integer := -1;
    Y : Integer := -1;
begin
   pragma Assert (X mod Y =  0);  -- @ASSERT:PASS
   pragma Assert (X mod Y = -1);  -- @ASSERT:FAIL
end;
