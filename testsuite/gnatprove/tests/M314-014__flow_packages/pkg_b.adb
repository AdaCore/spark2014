package body Pkg_B
  with Refined_State => (State_A => X,
                         State_B => Y,
                         State_C => Z)
is
   X : Integer;
   Y : Integer := 0;
   Z : Integer := 0;
begin
   X := Other.Y;    --  violates initializes contract
end Pkg_B;
