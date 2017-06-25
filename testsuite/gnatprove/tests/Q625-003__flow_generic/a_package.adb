package body A_Package
is

   procedure A_Generic_Procedure (S : in out My_State)
   is
   begin
      Do_It (S.State);
   end A_Generic_Procedure;


end A_Package;
