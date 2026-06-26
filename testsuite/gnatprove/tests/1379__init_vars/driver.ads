pragma Ada_2022;
with SPARK.Containers.Formal.Impl.Vectors;

package Driver with SPARK_Mode is
   subtype Small_Positive is Short_Integer range 1 .. Short_Integer'Last;

   package Small is new
     SPARK.Containers.Formal.Impl.Vectors (Small_Positive, Integer);
end Driver;
