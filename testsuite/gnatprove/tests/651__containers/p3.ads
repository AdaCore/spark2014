with SPARK.Containers.Functional.Sets;
package P3 with SPARK_Mode is
   type E is private;
private
   type E is new Integer with Type_Invariant => E >= 0, Default_Value => 0;
end P3;
