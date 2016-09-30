with GNAT.OS_Lib;            use GNAT.OS_Lib;

procedure Nest_In_Proc2 is
   -- it may not terminate because it is calling Proxy, which is nonreturning,
   -- but this is not detected

   procedure Proxy with Pre => True;

   procedure Proxy is
   begin
      OS_Exit (1);
   end;

   package Pkg is
      procedure Nothing;
   end Pkg;

   package body Pkg is
      procedure Nothing is
      begin
         null;
      end Nothing;
   begin
      Proxy; -- this call is not detected
   end Pkg;

begin
   null;
end Nest_In_Proc2;
