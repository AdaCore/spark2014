--  Define two allocators for objects of size 4 and 8

pragma Ada_2022;

with Allocator;
with Allocator.Base;
with Allocator.Ownership_Wrapper;
with Interfaces; use Interfaces;

package Types
  with SPARK_Mode
is
   Length_4 : constant Natural := 200;
   --  Maximal number of elements of size 4 that can be allocated in the buffer
   Length_8 : constant Natural := 100;
   --  Maximal number of elements of size 8 that can be allocated in the buffer

   type Byte_Array is array (Positive range <>) of Unsigned_8;

   --  Instance for 4

   subtype Byte_Array_4 is Byte_Array (1 .. 4);

   function Byte_Array_4_Eq (X, Y : Byte_Array_4) return Boolean
   is (X = Y)
   with Annotate => (GNATprove, Logical_Equal);

   type Binary_Object_Type_4 is record
      Data : Byte_Array_4;
   end record;

   function "=" (X, Y : Binary_Object_Type_4) return Boolean
   is (Byte_Array_4_Eq (X.Data, Y.Data))
   with Annotate => (GNATprove, Logical_Equal);
   --  This is really the normal builtin equality. It is only redefined to
   --  add the Logical_Equal annotation.

   package Base_4 is new
     Allocator.Base
       (Object_Size        => 4,
        Allocator_Length   => Length_4,
        Binary_Object_Type => Binary_Object_Type_4,
        Index_Base         => Integer_16);

   package Allocators_4 is new Allocator.Ownership_Wrapper
       (Object_Size        => 4,
        Allocator_Length   => Length_4,
        Binary_Object_Type => Binary_Object_Type_4,
        Index_Base         => Integer_16);

   --  Instance for 8

   subtype Byte_Array_8 is Byte_Array (1 .. 8);

   function Byte_Array_8_Eq (X, Y : Byte_Array_8) return Boolean
   is (X = Y)
   with Annotate => (GNATprove, Logical_Equal);

   type Binary_Object_Type_8 is record
      Data : Byte_Array_8;
   end record;

   function "=" (X, Y : Binary_Object_Type_8) return Boolean
   is (Byte_Array_8_Eq (X.Data, Y.Data))
   with Annotate => (GNATprove, Logical_Equal);
   --  This is really the normal builtin equality. It is only redefined to
   --  add the Logical_Equal annotation.

   package Base_8 is new
     Allocator.Base
       (Object_Size        => 8,
        Allocator_Length   => Length_8,
        Binary_Object_Type => Binary_Object_Type_8,
        Index_Base         => Integer_16);

   package Allocators_8 is new Allocator.Ownership_Wrapper
       (Object_Size        => 8,
        Allocator_Length   => Length_8,
        Binary_Object_Type => Binary_Object_Type_8,
        Index_Base         => Integer_16);

end Types;
