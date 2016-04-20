with Data2; use Data2;

package body Procs2
  with SPARK_Mode
is
   function Get return Boolean is
   begin
      return Data2.Val;
   end Get;
end Procs2;
