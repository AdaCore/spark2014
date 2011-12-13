package Pack is

   X : Boolean;

   procedure P0 (X : in out Boolean);

   procedure P1
     with Post => X = X'Old;  --  incorrect postcondition

   procedure P2 (X : in out Boolean)
     with Post => X = X'Old;  --  incorrect postcondition

   procedure P3;

   procedure P5
     with Post => X = X'Old;  --  incorrect postcondition

end;
