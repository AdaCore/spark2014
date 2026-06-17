--  Implement an allocator inside an array. It is entirely in SPARK and can be
--  verified by GNATprove.

pragma Ada_2022;

with Ada.Unchecked_Conversion;
with Interfaces;         use Interfaces;
with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Containers.Functional.Infinite_Sequences;
with SPARK.Containers.Functional.Maps;

generic
   Object_Size : Natural;
   --  Size of the object we want to store in byte
   Allocator_Length : Natural := 100;
   --  Maximal number of elements that can be allocated in the buffer
   type Binary_Object_Type is private;
   --  An array of Object_Size bytes
   type Index_Base is range <>;

package Allocator.Base with SPARK_Mode
is
   pragma
     Compile_Time_Error
       (Binary_Object_Type'Size /= 8 * Object_Size,
        "Binary_Object_Type should have Object_Size bytes");

   pragma Unevaluated_Use_Of_Old (Allow);

   subtype Extended_Index is
     Index_Base'Base
       range Index_Base'Base (-Allocator_Length)
             .. Index_Base'Base (Allocator_Length);

   pragma
     Compile_Time_Error
       (Extended_Index'Object_Size > 256 ** Object_Size,
        "length of allocator is too big");
   --  Make sure that there is enough room in the object to store the linked
   --  free list.

   type Padding_Type is
     array (Positive range 1 .. Object_Size - Extended_Index'Object_Size / 8)
     of Unsigned_8;

   type Memory_Cell_Type is record
      Next    : Extended_Index'Base;
      Padding : Padding_Type;
   end record
   with Alignment => 1;
   --  An object is a byte array of size Object_Size. Use the beginning of the
   --  array to store the index of the next free cell if the object is free. A
   --  negative number stands for the end of the buffer starting at -Next.

   function To_Object is new
     Ada.Unchecked_Conversion
       (Memory_Cell_Type,
        Binary_Object_Type)with Potentially_Invalid;

   function From_Object is new
     Ada.Unchecked_Conversion (Binary_Object_Type, Memory_Cell_Type);

   pragma Assert (Memory_Cell_Type'Object_Size = 8 * Object_Size);

   type Relaxed_Cell is record
      C : aliased Memory_Cell_Type;
   end record
   with Relaxed_Initialization;

   subtype Index_Type is Extended_Index range 1 .. Extended_Index'Last;
   type Memory_Type_Base is array (Index_Type range <>) of Relaxed_Cell;
   subtype Memory_Type is Memory_Type_Base (Index_Type);
   subtype Init_Memory_Type is Memory_Type_Base
   with Ghost_Predicate => (for all C of Init_Memory_Type => C'Initialized);

   Memory : Memory_Type;
   Free   : Extended_Index := -1;
   --  Buffer and first index of the free list. A negative number stands for
   --  the end of the buffer starting at -Free.

   package Memory_Index_Maps is new
     SPARK.Containers.Functional.Maps (Index_Type, Binary_Object_Type);
   use Memory_Index_Maps;
   package Memory_Index_Sequences is new
     SPARK.Containers.Functional.Infinite_Sequences
       (Index_Type,
        Use_Logical_Equality => True);
   use Memory_Index_Sequences;

   function Base_Invariant return Boolean
   with Ghost, Global => (Memory, Free);

   function Allocated_Cells return Memory_Index_Maps.Map
   with Ghost, Global => (Memory, Free), Pre => Base_Invariant;
   function Free_Cells return Memory_Index_Sequences.Sequence
   with Ghost, Global => (Memory, Free), Pre => Base_Invariant;
   --  The model of the buffer is a pair of a map of allocated indices mapped to
   --  the object stored at the index and a sequence of all indices in the free
   --  list.

   function Model_Invariant
     (Allocated_Cells : Memory_Index_Maps.Map;
      Free_Cells      : Memory_Index_Sequences.Sequence) return Boolean
   is ((for all I of Free_Cells => not Has_Key (Allocated_Cells, I))
       and
         Memory_Index_Sequences.Length (Free_Cells)
         + Memory_Index_Maps.Length (Allocated_Cells)
         = To_Big_Integer (Allocator_length))
   with Ghost, Global => null;

   function Invariant return Boolean
   with
     Ghost,
     Global => (Memory, Free),
     Post   =>
       (if Invariant'Result
        then
          Base_Invariant
          and then Model_Invariant (Allocated_Cells, Free_Cells));

   function Allocate (O : Binary_Object_Type) return Index_Type
   with
     Side_Effects,
     Global => (In_Out => (Memory, Free)),
     Pre    => Invariant and then Length (Free_Cells) > 0,
     Post   =>
       Invariant
       and then Allocated_Cells'Old <= Allocated_Cells
       and then
         Keys_Included_Except
           (Allocated_Cells, Allocated_Cells'Old, Allocate'Result)
       and then not Has_Key (Allocated_Cells'Old, Allocate'Result)
       and then Has_Key (Allocated_Cells, Allocate'Result)
       and then Get (Allocated_Cells, Allocate'Result) = O
       and then Length (Allocated_Cells) = Length (Allocated_Cells'Old) + 1
       and then Length (Free_Cells) = Length (Free_Cells'Old) - 1
       and then Free_Cells < Free_Cells'Old
       and then Allocate'Result = Get (Free_Cells'Old, Last (Free_Cells'Old));

   procedure Deallocate (I : Index_Type)
   with
     Global => (In_Out => (Memory, Free)),
     Pre    => Invariant and then Has_Key (Allocated_Cells, I),
     Post   =>
       Invariant
       and then Allocated_Cells <= Allocated_Cells'Old
       and then Keys_Included_Except (Allocated_Cells'Old, Allocated_Cells, I)
       and then not Has_Key (Allocated_Cells, I)
       and then Length (Allocated_Cells) = Length (Allocated_Cells'Old) - 1
       and then Length (Free_Cells) = Length (Free_Cells'Old) + 1
       and then Free_Cells'Old < Free_Cells
       and then I = Get (Free_Cells, Last (Free_Cells));

   function Deref (I : Index_Type) return Binary_Object_Type
   with
     Global => (Input => Memory, Proof_In => Free),
     Pre    => Invariant and then Has_Key (Allocated_Cells, I),
     Post   => Deref'Result = Get (Allocated_Cells, I);

   --  It is not possible to provide Constant_Reference and Reference functions
   --  for now as global inputs cannot be borrowed/observed.

end Allocator.Base;
