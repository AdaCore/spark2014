with GNAT.OS_Lib;            use GNAT.OS_Lib;
procedure Nest_In_Proc is
   pragma Annotate (GNATprove, Terminating, Nest_In_Proc);
   package Pkg is
      procedure Nothing;
      package Pkg2 is
         procedure Nothing2;
      end Pkg2;
   end Pkg;

   package body Pkg is
      procedure Nothing is
         pragma Annotate (GNATprove, Terminating, Nothing);
      begin
         null;
      end Nothing;
      package body Pkg2 is
         procedure Nothing2 is null;
      begin
         while True loop
            null;
         end loop;
      end Pkg2;
   begin
      null;
   end Pkg;
begin
   null;
end Nest_In_Proc;
