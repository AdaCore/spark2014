pragma Ada_2022;

package body Allocator.Pools
  with
    SPARK_Mode,
    Refined_State =>
      (Memory_4  => (Wrapper_4.The_Memory),
       Memory_8  => (Wrapper_8.The_Memory),
       Memory_16 => (Wrapper_16.The_Memory),
       Memory_32 => (Wrapper_32.The_Memory),
       Memory_64 => (Wrapper_64.The_Memory))
is

   -----------
   -- Codec --
   -----------

   package body Codec
     with SPARK_Mode
   is

      package ACC is new
        SPARK
          .Conversions
          .Access_Conversions
          .Access_Constant_Conversions_Potentially_Invalid
          (Storage_Type,
           Padded);

      package ACV is new
        SPARK
          .Conversions
          .Access_Conversions
          .Access_Variable_Conversions_Potentially_Invalid
          (Storage_Type,
           Padded);

      function Constant_Reference
        (S : not null access constant Storage_Type)
         return not null access constant Object_Type
      is (ACC.Convert_Constant_Access (S).Obj'Access);

      function Reference
        (S : not null access Storage_Type) return not null access Object_Type
      is (ACV.Convert_Access (S).Obj'Access);

   end Codec;

end Allocator.Pools;
