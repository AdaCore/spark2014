with Remote;

package body Handlers with SPARK_Mode is

   procedure P is
   begin
      V := not V;
   end;

   function F return Boolean is
   begin
      V := not V;
      return V;
   end F;

   P_Local : No_Param_Proc := P'Access;
   F_Local : No_Param_Fun  := F'Access;

   P_Remote : No_Param_Proc := Remote.P'Access;
   F_Remote : No_Param_Fun  := Remote.F'Access;
   H_Remote : No_Param_Proc := Remote.Heap'Access;

end Handlers;
