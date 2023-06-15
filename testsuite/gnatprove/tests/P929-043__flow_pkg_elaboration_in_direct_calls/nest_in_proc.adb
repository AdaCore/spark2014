with GNAT.OS_Lib; use GNAT.OS_Lib;

procedure Nest_In_Proc with Always_Terminates is

   procedure Proxy with Pre => True;

   procedure Proxy is
   begin
      OS_Exit (1);
   end;

   package Pkg with Always_Terminates is
      procedure Nothing;
   end Pkg;

   package body Pkg is
      procedure Nothing is
      begin
         null;
      end Nothing;
   begin
      Proxy;
   end Pkg;

begin
   null;
end Nest_In_Proc;
