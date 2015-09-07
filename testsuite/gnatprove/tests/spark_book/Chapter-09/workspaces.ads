pragma SPARK_Mode (On);
package Workspaces is
   type Workspace_Type is array (Positive range <>) of Natural;
   function Generate_Workspace (Size : in Positive) return Workspace_Type;
end Workspaces;

