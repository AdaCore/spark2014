with GNAT.OS_Lib;       use GNAT.OS_Lib;
with Nonreturning_Spec; use Nonreturning_Spec; pragma Elaborate_All (Nonreturning_Spec);

package body Functions is

   function Non_Ter_Func return Boolean is
   begin
      while True loop
         return True;
      end loop;
      return False;
   end Non_Ter_Func;

   procedure G is
   begin
      P;
   end G;

   package body Nested is
      procedure Nested_Proc is
      begin
         P;
      end Nested_Proc;
   begin
      Nested_Proc;
   end Nested;

begin
   G;
end Functions;
