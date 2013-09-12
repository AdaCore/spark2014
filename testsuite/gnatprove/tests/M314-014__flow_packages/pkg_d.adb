package body Pkg_D
is
begin
   X := Other.Y;   --  should be other.x
   Y := 5;         --  should be other.y
   Z := Other.X;   --  should be null
end Pkg_D;
