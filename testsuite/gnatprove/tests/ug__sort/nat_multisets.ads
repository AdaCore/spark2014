pragma SPARK_Mode (On);

with SPARK.Containers.Functional.Multisets;

package Nat_Multisets is new SPARK.Containers.Functional.Multisets (Natural, "=");
