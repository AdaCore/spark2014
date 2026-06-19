pragma Ada_2022;

package body Allocator.Pools.Sized_32
  with SPARK_Mode
is

   -----------
   -- Deref --
   -----------

   function Deref (P : Object_Pointer) return Object_Type
   is (case P.Pointer.Kind is
         when In_32       => Codec_32.Load (Wrapper_32.Deref (P.Pointer.P32)),
         when In_64       => Codec_64.Load (Wrapper_64.Deref (P.Pointer.P64)),
         when None_Bucket => raise Program_Error);

   ------------------------
   -- Constant_Reference --
   ------------------------

   function Constant_Reference
     (P : Object_Pointer) return not null access constant Object_Type is
   begin
      case P.Pointer.Kind is

         when In_32       =>
            return
              Codec_32.Constant_Reference
                (Wrapper_32.Constant_Reference (P.Pointer.P32));

         when In_64       =>
            return
              Codec_64.Constant_Reference
                (Wrapper_64.Constant_Reference (P.Pointer.P64));

         when None_Bucket =>
            raise Program_Error;
      end case;
   end Constant_Reference;

   ---------------
   -- Reference --
   ---------------

   function Reference
     (P : in out Object_Pointer) return not null access Object_Type is
   begin
      case P.Pointer.Kind is
         when In_32       =>
            return Codec_32.Reference (Wrapper_32.Reference (P.Pointer.P32));

         when In_64       =>
            return Codec_64.Reference (Wrapper_64.Reference (P.Pointer.P64));

         when None_Bucket =>
            raise Program_Error;
      end case;
   end Reference;

   --------------
   -- Allocate --
   --------------

   function Allocate (O : Object_Type) return Object_Pointer is
   begin
      if not Wrapper_32.Is_Full then
         declare
            Cell : Wrapper_32.Object_Pointer;
         begin
            Cell := Wrapper_32.Allocate (Codec_32.To_Storage (O));
            return (Pointer => (Kind => In_32, P32 => Cell));
         end;
      else
         declare
            Cell : Wrapper_64.Object_Pointer;
         begin
            Cell := Wrapper_64.Allocate (Codec_64.To_Storage (O));
            return (Pointer => (Kind => In_64, P64 => Cell));
         end;
      end if;
   end Allocate;

   ----------------
   -- Deallocate --
   ----------------

   procedure Deallocate (P : in out Object_Pointer) is
   begin
      case P.Pointer.Kind is
         when None_Bucket =>
            null;

         when In_32       =>
            Wrapper_32.Deallocate (P.Pointer.P32);
            P := (Pointer => (Kind => None_Bucket));

         when In_64       =>
            Wrapper_64.Deallocate (P.Pointer.P64);
            P := (Pointer => (Kind => None_Bucket));
      end case;
   end Deallocate;

end Allocator.Pools.Sized_32;
