with Procs; use Procs;
pragma Elaborate_All (Procs);
with Procs2;
pragma Elaborate_All (Procs2);

package Globs
  with SPARK_Mode
is
   pragma Elaborate_Body;
   X : Boolean := Procs.Get;
   Y : Boolean;
end Globs;
