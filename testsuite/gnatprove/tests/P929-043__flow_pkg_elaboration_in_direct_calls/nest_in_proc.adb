with GNAT.OS_Lib;            use GNAT.OS_Lib;

procedure Nest_In_Proc is
   -- this proves to be terminating because the call to Pkg is not considered
   -- relevant right now

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
end Nest_In_Proc;
