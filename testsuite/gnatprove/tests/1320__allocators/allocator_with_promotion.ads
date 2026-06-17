--  Define an allocator for objects of size 4 that can use the allocator for
--  objects of size 8 if the allocator for objects of size 4 is full. It is
--  entirely in SPARK and can be verified with GNATprove.

with Types;              use Types;
with Allocator;          use Allocator;
with SPARK.Big_Integers; use SPARK.Big_Integers;

package Allocator_With_Promotion
  with SPARK_Mode
is

   type Object_Pointer is private
   with Default_Initial_Condition => Is_Null (Object_Pointer);

   function Is_Null (P : Object_Pointer) return Boolean;

   function Is_Promoted (P : Object_Pointer) return Boolean
   with Ghost, Global => null;

   function Deref (P : Object_Pointer) return Binary_Object_Type_4
   with Global => null, Pre => not Is_Null (P);

   function Constant_Reference
     (P : Object_Pointer) return not null access constant Binary_Object_Type_4
   with
     Global => null,
     Pre    => not Is_Null (P),
     Post   => Constant_Reference'Result.all = Deref (P);

   function At_End
     (X : access constant Binary_Object_Type_4)
      return access constant Binary_Object_Type_4
   is (X)
   with Ghost, Annotate => (GNATprove, At_End_Borrow);

   function At_End (X : Object_Pointer) return Object_Pointer
   is (X)
   with Ghost, Annotate => (GNATprove, At_End_Borrow);

   function Reference
     (P : in out Object_Pointer) return not null access Binary_Object_Type_4
   with
     Global => null,
     Pre    => not Is_Null (P),
     Post   =>
       not Is_Null (At_End (P))
       and then At_End (Reference'Result).all = Deref (At_End (P));

   function Allocate (O : Binary_Object_Type_4) return Object_Pointer
   with
     Side_Effects,
     Global         =>
       (In_Out => (Allocators_4.The_Memory, Allocators_8.The_Memory)),
     Pre            => Allocators_4.Num_Free > 0 or Allocators_8.Num_Free > 0,
     Post           =>
       not Is_Null (Allocate'Result) and then Deref (Allocate'Result) = O,
     Contract_Cases =>
       (Allocators_4.Num_Free = 0 =>
          Allocators_4.Num_Free = 0
          and Allocators_8.Num_Free = Allocators_8.Num_Free'Old - 1,
        others                    =>
          Allocators_4.Num_Free = Allocators_4.Num_Free'Old - 1
          and Allocators_8.Num_Free = Allocators_8.Num_Free'Old);

   procedure Deallocate (P : in out Object_Pointer)
   with
     Global         =>
       (In_Out => (Allocators_4.The_Memory, Allocators_8.The_Memory)),
     Post           => Is_Null (P),
     Contract_Cases =>
       (Is_Null (P)     =>
          Allocators_4.Num_Free = Allocators_4.Num_Free'Old
          and Allocators_8.Num_Free = Allocators_8.Num_Free'Old,
        Is_Promoted (P) =>
          Allocators_4.Num_Free = Allocators_4.Num_Free'Old
          and Allocators_8.Num_Free = Allocators_8.Num_Free'Old + 1,
        others          =>
          Allocators_4.Num_Free = Allocators_4.Num_Free'Old + 1
          and Allocators_8.Num_Free = Allocators_8.Num_Free'Old);

private
   use Allocators_4;
   use Allocators_8;

   type Promotion_Kind is (None, Promoted);

   type Object_Pointer (Kind : Promotion_Kind := None) is record
      case Kind is
         when None =>
            Ptr : Allocators_4.Object_Pointer;

         when Promoted =>
            Promoted_Ptr : Allocators_8.Object_Pointer;
      end case;
   end record;

   function Is_Null (P : Object_Pointer) return Boolean
   is (case P.Kind is
         when None     => Is_Null (P.Ptr),
         when Promoted => Is_Null (P.Promoted_Ptr));

   function Is_Promoted (P : Object_Pointer) return Boolean
   is (not Is_Null (P) and then P.Kind /= None);

end Allocator_With_Promotion;
