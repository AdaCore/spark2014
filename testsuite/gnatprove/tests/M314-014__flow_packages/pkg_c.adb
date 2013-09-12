package body Pkg_C
  with Refined_State => (State_A => X,
                         State_B => Y,
                         State_C => Z)
is
   X : Integer := 0;
   Y : Integer;
   Z : Integer;
begin
   Y := Other.X;    --  use of uninitialized state Other.X
                    --  also violdates contract as other.state_d is not used

   Z := 55;         --  State_C is not meant to be initialized

   Other.X := 12;   --  can only initialize my own state
end Pkg_C;
