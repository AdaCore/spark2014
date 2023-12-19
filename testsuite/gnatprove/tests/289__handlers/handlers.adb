package body Handlers with SPARK_Mode is

   procedure P_Incr is
   begin
      V := V + 1;
   end P_Incr;

   function F_Incr return Integer is
   begin
      V := V + 1;
      return V;
   end F_Incr;

   P : No_Param_Proc := P_Incr'Access; --@WEAKER_PRE_ACCESS:FAIL
   F : No_Param_Fun := F_Incr'Access; --@WEAKER_PRE_ACCESS:FAIL

end Handlers;
