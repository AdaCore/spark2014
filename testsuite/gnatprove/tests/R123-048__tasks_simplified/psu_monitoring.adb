pragma Profile (Ravenscar);
pragma SPARK_Mode;

with PSU_Simulation; use PSU_Simulation;

package body PSU_Monitoring is

   protected body Monitoring is
      procedure Set (X : in Monitor) is
      begin
         null;
      end Set;
   end Monitoring;

end PSU_Monitoring;
