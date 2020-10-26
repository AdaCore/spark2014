pragma SPARK_Mode;

with SPARK.Long_Integer_Conversions; use SPARK.Long_Integer_Conversions;

with SPARK.Arithmetic_Lemmas; pragma Elaborate_All (SPARK.Arithmetic_Lemmas);

package SPARK.Long_Integer_Arithmetic_Lemmas is new
  SPARK.Arithmetic_Lemmas (Long_Integer, To_Big_Integer);
