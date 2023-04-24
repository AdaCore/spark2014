with GNAT.OS_Lib; use GNAT.OS_Lib;

procedure Nest_In_Proc is

   procedure Proxy (X : Boolean) with Pre => X, No_Return, Exceptional_Cases => (others => False);

   procedure Proxy (X : Boolean) is
   begin
      pragma Assert (X);
      OS_Exit (1);
   end;

begin
   Proxy (False);
end Nest_In_Proc;
