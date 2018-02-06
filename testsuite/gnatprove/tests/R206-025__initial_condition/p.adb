with Q;

procedure P is
begin
   pragma Assert (Q.X); --  @ASSERT:FAIL
   --  This is only true when P is executed as a main subprogram,
   --  but false when it is called after Q.X has been modified.
end;
