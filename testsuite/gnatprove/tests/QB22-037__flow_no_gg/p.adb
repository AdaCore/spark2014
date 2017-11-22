package body P with Refined_State => (S => (X, Y)) is
   X : Integer := 0;
   Y : Integer := 0;
   function Get_Half return Integer is (X);
   --  "Refined_Global => X" is intentionally missing
end;
