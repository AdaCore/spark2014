with SPARK.Containers.Formal.Indefinite_Vectors;
with Ada.Containers; use Ada.Containers;

package Processors with SPARK_Mode is
   type VCpuIdType is new Positive;
   type VCpuType is private;

   procedure DoStuff (VCpu : in out VCpuType) with Import;

   procedure DoOtherStuff (VCpu1, VCpu2 : in out VCpuType) with Import;

private

   type VCpuType is record
      X, Y : Integer;
   end record with Size => 64;

end Processors;
