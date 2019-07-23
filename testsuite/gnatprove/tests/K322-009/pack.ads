package Pack is

   X : Boolean;

   procedure P0 (X : in out Boolean);

   procedure P1
     with Post => X = X'Old;  --  @POSTCONDITION:FAIL

   procedure P2 (X : in out Boolean)
     with Post => X = X'Old;  --  @POSTCONDITION:FAIL

   procedure P3;

   procedure P5
     with Post => X = X'Old;  --  @POSTCONDITION:FAIL

end;
