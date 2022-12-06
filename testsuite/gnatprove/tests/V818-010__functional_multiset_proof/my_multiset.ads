pragma SPARK_Mode (On);

with SPARK.Containers.Functional.Multisets;
with Types; use Types;

package My_Multiset is
  new SPARK.Containers.Functional.Multisets
     (Private_Type, Eq);
