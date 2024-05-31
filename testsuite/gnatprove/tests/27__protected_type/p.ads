pragma Profile (Jorvik);
pragma Partition_Elaboration_Policy (Sequential);

package P with SPARK_Mode is

   type T is private;

private
   type T is new Integer with Type_Invariant => T >= 0, Default_Value => 0;
end P;
