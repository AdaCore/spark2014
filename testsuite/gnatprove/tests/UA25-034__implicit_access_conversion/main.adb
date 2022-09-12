with SPARK.Containers.Formal.Indefinite_Vectors;
with Ada.Containers; use Ada.Containers;
with Processors; use Processors;

procedure Main with SPARK_Mode is

   package VCpuVectors is new SPARK.Containers.Formal.Indefinite_Vectors
     (Index_Type                   => VCpuIdType,
      Element_Type                 => VCpuType,
      Max_Size_In_Storage_Elements => VCpuType'Size);
   use all type VCpuVectors.Vector;

   VCpuVector : aliased VCpuVectors.Vector (10);

   procedure UseCase(VCpuId : VCpuIdType)
     with Pre => VCpuId in 1 .. VCpuVectors.Last_Index (VCpuVector)
   is
      VCpuVectorAcc : constant access VCpuVectors.Vector := VCpuVector'Access;
      VCpu          : access VCpuType := VCpuVectors.Reference (VCpuVectorAcc, VCpuId);
   begin
      DoStuff(VCpu.all);
   end UseCase;

begin
   null;
end;
