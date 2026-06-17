--  Define an allocator for typed objects of size 8 on top of the wrappers
--  with ownership defined in Types. It is entirely in SPARK and can be verified
--  with GNATprove.

pragma Ada_2022;

with Ada.Unchecked_Conversion;
with Allocator;          use Allocator;
with Types;              use Types;
with Interfaces;         use Interfaces;
with SPARK.Big_Integers; use SPARK.Big_Integers;

package Typed_Allocator
  with SPARK_Mode
is
   use Types.Allocators_8;

   type Object_Type is record
      F1 : Integer_32;
      F2 : Unsigned_16;
      F3 : Boolean;
      F4 : Integer_8;
   end record
   with Object_Size => 64, Alignment => 1;

   type Object_Pointer is private
   with Default_Initial_Condition => Is_Null (Object_Pointer);

   function Is_Null (P : Object_Pointer) return Boolean
   with Global => null;

   function Deref (P : Object_Pointer) return Object_Type
   with Global => null, Pre => not Is_Null (P);

   function Constant_Reference
     (P : Object_Pointer) return access constant Object_Type
   with
     Global => null,
     Pre    => not Is_Null (P),
     Post   => Constant_Reference'Result.all = Deref (P);

   function At_End
     (X : access constant Object_Type) return access constant Object_Type
   is (X)
   with Ghost, Annotate => (GNATprove, At_End_Borrow);

   function At_End (X : Object_Pointer) return Object_Pointer
   is (X)
   with Ghost, Annotate => (GNATprove, At_End_Borrow);

   function Reference
     (P : in out Object_Pointer) return not null access Object_Type
   with
     Global => null,
     Pre    => not Is_Null (P),
     Post   =>
       not Is_Null (At_End (P))
       and then At_End (Reference'Result).all = Deref (At_End (P));

   function Allocate (O : Object_Type) return Object_Pointer
   with
     Side_Effects,
     Global => (In_Out => The_Memory),
     Pre    => Num_Free > 0,
     Post   =>
       Num_Free = Num_Free'Old - 1
       and then not Is_Null (Allocate'Result)
       and then Deref (Allocate'Result) = O;

   procedure Deallocate (P : in out Object_Pointer)
   with
     Global         => (In_Out => The_Memory),
     Post           => Is_Null (P),
     Contract_Cases =>
       (Is_Null (P) => Num_Free = Num_Free'Old,
        others      => Num_Free = Num_Free'Old + 1);

private

   function From_Binary_Object is new
     Ada.Unchecked_Conversion
       (Binary_Object_Type_8,
        Object_Type)with Potentially_Invalid;

   type Object_Pointer is record
      Ptr : Allocators_8.Object_Pointer;
   end record
   with
     Predicate =>
       (if not Is_Null (Ptr)
        then From_Binary_Object (Deref (Ptr))'Valid_Scalars);

end Typed_Allocator;
