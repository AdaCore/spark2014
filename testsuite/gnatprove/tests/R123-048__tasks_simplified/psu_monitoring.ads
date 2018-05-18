pragma Profile (Ravenscar);
pragma SPARK_Mode;

pragma Partition_Elaboration_Policy (Sequential);
pragma Assertion_Policy (Pre => Check);

package PSU_Monitoring is

   type Monitor is record
      A : Integer;
   end record;

   protected type Monitoring is

      procedure Set (X : in Monitor);

   end Monitoring;

   Monitoring_Interface : Monitoring;

end PSU_Monitoring;
