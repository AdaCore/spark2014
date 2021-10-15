with Ada.Containers.Formal_Indefinite_Vectors;
with Ada.Containers; use Ada.Containers;

procedure Main with SPARK_Mode is
   type VCpuIdType is new Positive;
   type VCpuType is record
      X, Y : Integer;
   end record with Size => 64;

   package VCpuVectors is new Ada.Containers.Formal_Indefinite_Vectors
     (Index_Type                   => VCpuIdType,
      Element_Type                 => VCpuType,
      Max_Size_In_Storage_Elements => VCpuType'Size);
   use all type VCpuVectors.Vector;

   VCpuVector : aliased VCpuVectors.Vector (10);

   procedure DoStuff (VCpu : in out VCpuType) with Import;

   procedure DoOtherStuff (VCpu1, VCpu2 : in out VCpuType) with Import;

   procedure UseCase(VCpuId : VCpuIdType)
     with Pre => VCpuId in 1 .. VCpuVectors.Last_Index (VCpuVector)
   is
      VCpuVectorAcc : constant access VCpuVectors.Vector := VCpuVector'Access;
      pragma Assert (VCpuVectors.At_End (VCpuVectorAcc).Capacity = 10); --@ASSERT:PASS
      VCpu          : access VCpuType := VCpuVectors.Reference (VCpuVectorAcc, VCpuId);
      pragma Assert (VCpuVectors.At_End (VCpuVectorAcc).Capacity = 10);  --@ASSERT:PASS
   begin
      VCpu.x := VCpu.y;
      DoStuff(VCpu.all);
   end UseCase;

begin
   null;
end;
