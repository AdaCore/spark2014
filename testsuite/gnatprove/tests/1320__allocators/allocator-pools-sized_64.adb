pragma Ada_2022;

package body Allocator.Pools.Sized_64
  with SPARK_Mode
is

   -----------
   -- Deref --
   -----------

   function Deref (P : Object_Pointer) return Object_Type
   is (Codec_64.Load (Wrapper_64.Deref (P.Pointer)));

   ------------------------
   -- Constant_Reference --
   ------------------------

   function Constant_Reference
     (P : Object_Pointer) return not null access constant Object_Type is
   begin
      return
        Codec_64.Constant_Reference
          (Wrapper_64.Constant_Reference (P.Pointer));
   end Constant_Reference;

   ---------------
   -- Reference --
   ---------------

   function Reference
     (P : in out Object_Pointer) return not null access Object_Type is
   begin
      return Codec_64.Reference (Wrapper_64.Reference (P.Pointer));
   end Reference;

   --------------
   -- Allocate --
   --------------

   function Allocate (O : Object_Type) return Object_Pointer is
   begin
      declare
         Cell : Wrapper_64.Object_Pointer;
      begin
         Cell := Wrapper_64.Allocate (Codec_64.To_Storage (O));
         return (Pointer => Cell);
      end;
   end Allocate;

   ----------------
   -- Deallocate --
   ----------------

   procedure Deallocate (P : in out Object_Pointer) is
   begin
      Wrapper_64.Deallocate (P.Pointer);
   end Deallocate;

end Allocator.Pools.Sized_64;
