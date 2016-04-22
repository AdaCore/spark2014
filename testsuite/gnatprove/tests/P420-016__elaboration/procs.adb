with Data; use Data;

package body Procs
  with SPARK_Mode
is
   function Get return Boolean is
   begin
      return Data.Val;
   end Get;
end Procs;
