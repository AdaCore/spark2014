pragma SPARK_Mode (On);
package body Workspaces is

   function Generate_Workspace (Size : in Positive) return Workspace_Type is
      Workspace : Workspace_Type(1 .. Size) := (others => 0);
   begin
      for J in 1 .. Size / 2 loop
         Workspace (J) := J;
         Workspace ((Size + 1) - J) := J;
      end loop;
      return Workspace;
   end Generate_Workspace;

end Workspaces;

