with SPARK.Big_Integers; use SPARK.Big_Integers;

package P
  with SPARK_Mode
is
   Base : Big_Integer := 65536;
   pragma Assert (Base = 2 ** 16);
end;
