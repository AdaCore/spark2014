with Ada.Unchecked_Conversion;
with Interfaces;                           use Interfaces;
with SPARK.Conversions.Access_Conversions;
use SPARK.Conversions.Access_Conversions;

package body Allocator_With_Promotion
  with SPARK_Mode
is
   type Padding_Type is array (Positive range 1 .. 8 - 4) of Unsigned_8;

   type Promoted_Object_Type is record
      Object  : aliased Binary_Object_Type_4;
      Padding : Padding_Type;
   end record;

   pragma
     Assert
       (Promoted_Object_Type'Object_Size = Binary_Object_Type_8'Object_Size);

   function To_Promoted_Object is new
     Ada.Unchecked_Conversion (Binary_Object_Type_8, Promoted_Object_Type);
   function From_Promoted_Object is new
     Ada.Unchecked_Conversion (Promoted_Object_Type, Binary_Object_Type_8);

   package To_Promoted_Access_Conversions is new
     Access_Variable_Conversions (Binary_Object_Type_8, Promoted_Object_Type);

   function Deref (P : Object_Pointer) return Binary_Object_Type_4
   is (case P.Kind is
         when None     => Allocators_4.Deref (P.Ptr),
         when Promoted =>
           To_Promoted_Object (Allocators_8.Deref (P.Promoted_Ptr)).Object);

   function Constant_Reference
     (P : Object_Pointer) return not null access constant Binary_Object_Type_4
   is
   begin
      case P.Kind is
         when None     =>
            return Constant_Reference (P.Ptr);

         when Promoted =>
            return
              To_Promoted_Access_Conversions.Convert_Constant_Access
                (Constant_Reference (P.Promoted_Ptr))
                .Object'Access;
      end case;
   end Constant_Reference;

   function Reference
     (P : in out Object_Pointer) return not null access Binary_Object_Type_4 is
   begin
      case P.Kind is
         when None     =>
            return Reference (P.Ptr);

         when Promoted =>
            return
              To_Promoted_Access_Conversions.Convert_Access
                (Reference (P.Promoted_Ptr))
                .Object'Access;
      end case;
   end Reference;

   function Allocate (O : Binary_Object_Type_4) return Object_Pointer is
   begin
      if Allocators_4.Is_Full then
         declare
            Ptr : Allocators_8.Object_Pointer;
         begin
            Ptr := Allocate (From_Promoted_Object ((O, (others => 0))));
            return (Promoted, Ptr);
         end;
      else
         declare
            Ptr : Allocators_4.Object_Pointer;
         begin
            Ptr := Allocate (O);
            return (None, Ptr);
         end;
      end if;
   end Allocate;

   procedure Deallocate (P : in out Object_Pointer) is
   begin
      if Is_Null (P) then
         return;
      end if;

      case P.Kind is
         when None     =>
            Deallocate (P.Ptr);

         when Promoted =>
            Deallocate (P.Promoted_Ptr);
      end case;
   end Deallocate;

end Allocator_With_Promotion;
