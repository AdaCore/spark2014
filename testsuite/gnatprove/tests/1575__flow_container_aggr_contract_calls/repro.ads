with SPARK.Containers.Functional.Infinite_Sequences;
package Repro with SPARK_Mode is
   package Sequences is new
     SPARK.Containers.Functional.Infinite_Sequences (Integer);
   use Sequences;
   procedure Check (Value : Sequence)
   with Import, Global => null, Pre => Value = [1];
end Repro;
