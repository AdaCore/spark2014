with GNAT.OS_Lib; use GNAT.OS_Lib;

procedure Nest_In_Proc is

   procedure Proxy with No_Return;

   procedure Proxy is
   begin
      OS_Exit (1);
   end;

begin
   declare
      package Inner is
         procedure Dummy;
      end;

      package body Inner is
         procedure Dummy is null;
      begin
         Proxy;
      end;
   begin
      Proxy;
   end;
end Nest_In_Proc;
