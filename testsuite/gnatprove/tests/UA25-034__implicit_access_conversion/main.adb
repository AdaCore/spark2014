with SPARK.Containers.Formal.Unbounded_Vectors;
with Ada.Containers; use Ada.Containers;
with Processors; use Processors;

procedure Main with SPARK_Mode is

   package VCpuVectors is new SPARK.Containers.Formal.Unbounded_Vectors
     (Index_Type                   => VCpuIdType,
      Element_Type                 => VCpuType);
   use all type VCpuVectors.Vector;

   VCpuVector : aliased VCpuVectors.Vector;

   procedure UseCase(VCpuId : VCpuIdType)
     with Pre => VCpuId in 1 .. VCpuVectors.Last_Index (VCpuVector)
   is
      VCpu : access VCpuType := VCpuVectors.Reference (VCpuVector, VCpuId);
   begin
      DoStuff(VCpu.all);
   end UseCase;

begin
   null;
end;
