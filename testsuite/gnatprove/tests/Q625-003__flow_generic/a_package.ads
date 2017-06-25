package A_Package
is

   type My_State is private;

   generic
      with procedure Do_It (A : in out Integer);
   procedure A_Generic_Procedure (S : in out My_State)
     with Global => null;

private

   type My_State is record
      State : Integer;
   end record;

end A_Package;
