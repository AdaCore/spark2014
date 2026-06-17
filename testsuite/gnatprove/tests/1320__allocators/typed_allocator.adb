with SPARK.Conversions.Access_Conversions;
use SPARK.Conversions.Access_Conversions;

package body Typed_Allocator
  with SPARK_Mode
is

   package Object_Access_Conversions is new
     Access_Variable_Conversions_Potentially_Invalid
       (Binary_Object_Type_8,
        Object_Type);

   function To_Binary_Object is new
     Ada.Unchecked_Conversion (Object_Type, Binary_Object_Type_8);

   function Is_Null (P : Object_Pointer) return Boolean
   is (Is_Null (P.Ptr));

   function Deref (P : Object_Pointer) return Object_Type
   is (From_Binary_Object (Deref (P.Ptr)));

   function Constant_Reference
     (P : Object_Pointer) return access constant Object_Type is
   begin
      return
        Object_Access_Conversions.Convert_Constant_Access
          (Constant_Reference (P.Ptr));
   end Constant_Reference;

   function Reference
     (P : in out Object_Pointer) return not null access Object_Type is
   begin
      return Object_Access_Conversions.Convert_Access (Reference (P.Ptr));
   end Reference;

   function Allocate (O : Object_Type) return Object_Pointer is
      Ptr : Allocators_8.Object_Pointer;
   begin
      pragma Assert (From_Binary_Object (To_Binary_Object (O)) = O);
      Ptr := Allocators_8.Allocate (To_Binary_Object (O));
      return (Ptr => Ptr);
   end Allocate;

   procedure Deallocate (P : in out Object_Pointer) is
   begin
      Deallocate (P.Ptr);
   end Deallocate;

end Typed_Allocator;
