pragma Ada_2022;

with Allocator.Ownership_Wrapper;
with Ada.Unchecked_Conversion;
with Interfaces;         use Interfaces;
with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Conversions.Access_Conversions;

--  Outer generic. It creates, hidden in its private part, five byte-array
--  allocators (cells of 4, 8, 16, 32 and 64 bytes) on top of Allocator.Base +
--  Allocator.Base.Ownership_Wrapper. It exposes only Num_Free_4 .. Num_Free_64:
--  the number of free cells in each bucket (one per size, since the free count
--  is a property of the shared bucket).
--
--  The private part also holds the conversion helper Codec, used by the five
--  per-size wrappers (the generic children Allocator.Pools.Sized_*) to view a
--  byte-array cell as the object it holds.

generic
   Length_4 : Natural := 0;
   Length_8 : Natural := 0;
   Length_16 : Natural := 0;
   Length_32 : Natural := 0;
   Length_64 : Natural := 0;
package Allocator.Pools with
    SPARK_Mode,
    Abstract_State    => (Memory_4, Memory_8, Memory_16, Memory_32, Memory_64),
    Initializes       => (Memory_4, Memory_8, Memory_16, Memory_32, Memory_64),
    Initial_Condition =>
      Num_Free_4 = To_Big_Integer (Length_4)
      and Num_Free_8 = To_Big_Integer (Length_8)
      and Num_Free_16 = To_Big_Integer (Length_16)
      and Num_Free_32 = To_Big_Integer (Length_32)
      and Num_Free_64 = To_Big_Integer (Length_64)
is

   --  Number of free cells in each bucket.

   function Num_Free_4 return Big_Natural
   with Ghost, Global => Memory_4;
   function Num_Free_8 return Big_Natural
   with Ghost, Global => Memory_8;
   function Num_Free_16 return Big_Natural
   with Ghost, Global => Memory_16;
   function Num_Free_32 return Big_Natural
   with Ghost, Global => Memory_32;
   function Num_Free_64 return Big_Natural
   with Ghost, Global => Memory_64;

private

   type Byte_Array is array (Positive range <>) of Unsigned_8;

   subtype Byte_Array_4 is Byte_Array (1 .. 4);
   subtype Byte_Array_8 is Byte_Array (1 .. 8);
   subtype Byte_Array_16 is Byte_Array (1 .. 16);
   subtype Byte_Array_32 is Byte_Array (1 .. 32);
   subtype Byte_Array_64 is Byte_Array (1 .. 64);

   type Storage_4 is record
      Data : Byte_Array_4;
   end record
   with Alignment => 4;
   type Storage_8 is record
      Data : Byte_Array_8;
   end record
   with Alignment => 4;
   type Storage_16 is record
      Data : Byte_Array_16;
   end record
   with Alignment => 4;
   type Storage_32 is record
      Data : Byte_Array_32;
   end record
   with Alignment => 4;
   type Storage_64 is record
      Data : Byte_Array_64;
   end record
   with Alignment => 4;

   --  Redefined equalities carrying the Logical_Equal annotation. They are the
   --  ordinary record equality, needed (and visible) when Allocator.Base
   --  instantiates the functional Maps over the storage type.

   function L_Eq_4 (X, Y : Byte_Array_4) return Boolean
   is (X = Y)
   with Annotate => (GNATprove, Logical_Equal);
   function L_Eq_8 (X, Y : Byte_Array_8) return Boolean
   is (X = Y)
   with Annotate => (GNATprove, Logical_Equal);
   function L_Eq_16 (X, Y : Byte_Array_16) return Boolean
   is (X = Y)
   with Annotate => (GNATprove, Logical_Equal);
   function L_Eq_32 (X, Y : Byte_Array_32) return Boolean
   is (X = Y)
   with Annotate => (GNATprove, Logical_Equal);
   function L_Eq_64 (X, Y : Byte_Array_64) return Boolean
   is (X = Y)
   with Annotate => (GNATprove, Logical_Equal);

   function "=" (X, Y : Storage_4) return Boolean
   is (L_Eq_4 (X.Data, Y.Data))
   with Annotate => (GNATprove, Logical_Equal);
   function "=" (X, Y : Storage_8) return Boolean
   is (L_Eq_8 (X.Data, Y.Data))
   with Annotate => (GNATprove, Logical_Equal);
   function "=" (X, Y : Storage_16) return Boolean
   is (L_Eq_16 (X.Data, Y.Data))
   with Annotate => (GNATprove, Logical_Equal);
   function "=" (X, Y : Storage_32) return Boolean
   is (L_Eq_32 (X.Data, Y.Data))
   with Annotate => (GNATprove, Logical_Equal);
   function "=" (X, Y : Storage_64) return Boolean
   is (L_Eq_64 (X.Data, Y.Data))
   with Annotate => (GNATprove, Logical_Equal);

   --------------------------------------------------------------------------
   --  Codec: reinterprets a storage cell as the object it holds. The object
   --  occupies the first Object_Type'Object_Size bits of the cell, the rest
   --  being padding. The reinterpretation goes through a same-sized padded
   --  record (Padded), so the Unchecked_Conversions relate two equally sized
   --  types. An Object_Type unfit for unchecked conversion is rejected at
   --  instantiation; From_Raw is Potentially_Invalid so the codec also accepts
   --  objects whose representation may carry invalid values.
   --------------------------------------------------------------------------

   generic
      type Object_Type is private;
      type Storage_Type is private;
      Bucket_Bytes : Positive;
      Object_Bytes : Positive;
      --  Size of Object_Type in bytes. Passed explicitly (rather than reading
      --  Object_Type'Object_Size inside the padding array bound) because using
      --  'Object_Size in a type definition that then feeds Unchecked_Conversion
      --  trips a GNATprove limitation. The pragma below checks it is correct.
   package Codec with SPARK_Mode is

      pragma
        Compile_Time_Error
          (Storage_Type'Object_Size /= 8 * Bucket_Bytes,
           "Storage_Type must be Bucket_Bytes bytes wide");
      pragma
        Compile_Time_Error
          (Object_Type'Object_Size /= 8 * Object_Bytes,
           "Object_Bytes must be Object_Type's size in bytes");
      pragma
        Compile_Time_Error
          (Object_Bytes > Bucket_Bytes,
           "Object_Type does not fit in the bucket");

      --  Non-executable logical equality on Object_Type, used in the contracts
      --  in place of a generic "=" formal.
      function Obj_Eq (X, Y : Object_Type) return Boolean
      with
        Ghost,
        Import,
        Global   => null,
        Annotate => (GNATprove, Logical_Equal);

      --  Component_Size => 8 lets gnatprove compute that this array (whose
      --  bound is not statically known inside the generic) tiles its bits
      --  exactly, so Padded is a suitable source/target for unchecked
      --  conversion (no unmodelled "unused bits").
      type Padding is
        array (Positive range 1 .. Bucket_Bytes - Object_Bytes)
        of aliased Unsigned_8
      with Component_Size => 8;

      type Padded is record
         Obj : aliased Object_Type;
         Pad : Padding;
      end record
      with Alignment => 4;

      pragma
        Compile_Time_Error
          (Padded'Object_Size /= 8 * Bucket_Bytes,
           "Object_Type cannot be tightly packed into the bucket");

      function To_Raw is new Ada.Unchecked_Conversion (Padded, Storage_Type);

      function From_Raw is new
        Ada.Unchecked_Conversion
          (Storage_Type,
           Padded)with Potentially_Invalid;

      function To_Storage (O : Object_Type) return Storage_Type
      is (To_Raw ((Obj => O, Pad => [others => 0])))
      with Global => null;

      function Load (S : Storage_Type) return Object_Type
      is (From_Raw (S).Obj)
      with Global => null, Pre => From_Raw (S)'Valid_Scalars;

      --  Reading back what was stored yields the same object.
      function Roundtrip (O : Object_Type) return Boolean
      is (Obj_Eq (Load (To_Storage (O)), O))
      with Ghost, Global => null, Post => Roundtrip'Result;

      --  Access-typed views of a live cell as the object it holds.

      function At_End
        (X : access constant Object_Type) return access constant Object_Type
      is (X)
      with Ghost, Annotate => (GNATprove, At_End_Borrow);
      function At_End
        (X : access constant Storage_Type) return access constant Storage_Type
      is (X)
      with Ghost, Annotate => (GNATprove, At_End_Borrow);

      function Constant_Reference
        (S : not null access constant Storage_Type)
         return not null access constant Object_Type
      with
        Global => null,
        Pre    => From_Raw (S.all)'Valid_Scalars,
        Post   => Obj_Eq (Constant_Reference'Result.all, Load (S.all));

      function Reference
        (S : not null access Storage_Type) return not null access Object_Type
      with
        Global => null,
        Pre    => From_Raw (S.all)'Valid_Scalars,
        Post   =>
          From_Raw (At_End (S).all)'Valid_Scalars
          and then
            Obj_Eq (At_End (Reference'Result).all, Load (At_End (S).all));

   end Codec;

   package Wrapper_4 is new
     Ownership_Wrapper
       (4,
        Length_4,
        Storage_4,
        Integer_16)with Part_Of => Memory_4;
   package Wrapper_8 is new
     Ownership_Wrapper
       (8,
        Length_8,
        Storage_8,
        Integer_16)with Part_Of => Memory_8;
   package Wrapper_16 is new
     Ownership_Wrapper
       (16,
        Length_16,
        Storage_16,
        Integer_16)with Part_Of => Memory_16;
   package Wrapper_32 is new
     Ownership_Wrapper
       (32,
        Length_32,
        Storage_32,
        Integer_16)with Part_Of => Memory_32;
   package Wrapper_64 is new
     Ownership_Wrapper
       (64,
        Length_64,
        Storage_64,
        Integer_16)with Part_Of => Memory_64;

   function Num_Free_4 return Big_Natural
   is (Wrapper_4.Num_Free);
   function Num_Free_8 return Big_Natural
   is (Wrapper_8.Num_Free);
   function Num_Free_16 return Big_Natural
   is (Wrapper_16.Num_Free);
   function Num_Free_32 return Big_Natural
   is (Wrapper_32.Num_Free);
   function Num_Free_64 return Big_Natural
   is (Wrapper_64.Num_Free);

end Allocator.Pools;
