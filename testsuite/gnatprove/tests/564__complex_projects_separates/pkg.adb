package body Pkg is

   package Pack is
      procedure P (X : in out Integer);
   end Pack;

   procedure P (X : in out Integer) is separate;

   package body Pack is separate;

end Pkg;
