--  Wrapper that provides the functionalities of the allocator in
--  Base, but separates the elements in the memory so that they are considered
--  as independent objects for verification. This is sound because array cells
--  have ownership so they can be no alias between the different cells. The
--  implementation cannot be verified by GNATprove.

pragma Ada_2022;

with SPARK.Big_Integers; use SPARK.Big_Integers;
private with Allocator.Base;

generic
   Object_Size : Natural;
   --  Size of the object we want to store in byte
   Allocator_Length : Natural := 100;
   --  Maximal number of elements that can be allocated in the buffer
   type Binary_Object_Type is private;
   --  An array of Object_Size bytes
   type Index_Base is range <>;

package Allocator.Ownership_Wrapper with
    SPARK_Mode,
    Abstract_State    => The_Memory,
    Initializes       => The_Memory,
    Initial_Condition => Num_Free = To_Big_Integer (Allocator_Length)
is
   pragma
     Compile_Time_Error
       (Binary_Object_Type'Size /= 8 * Object_Size,
        "Binary_Object_Type should have Object_Size bytes");

   type Object_Pointer is private
   with
     Annotate                  => (GNATprove, Ownership, "Needs_Reclamation"),
     Default_Initial_Condition => Is_Null (Object_Pointer);

   function Is_Null (P : Object_Pointer) return Boolean
   with Annotate => (GNATprove, Ownership, "Is_Reclaimed");

   function Num_Free return Big_Natural
   with Ghost, Global => The_Memory;

   function Deref (P : Object_Pointer) return Binary_Object_Type
   with Global => null, Pre => not Is_Null (P);

   function Is_Full return Boolean
   with Global => The_Memory, Post => Is_Full'Result = (Num_Free = 0);

   function Constant_Reference
     (P : Object_Pointer) return not null access constant Binary_Object_Type
   with
     Global => null,
     Pre    => not Is_Null (P),
     Post   => Constant_Reference'Result.all = Deref (P);

   function At_End
     (X : access constant Binary_Object_Type)
      return access constant Binary_Object_Type
   is (X)
   with Ghost, Annotate => (GNATprove, At_End_Borrow);

   function At_End (X : Object_Pointer) return Object_Pointer
   is (X)
   with Ghost, Annotate => (GNATprove, At_End_Borrow);

   function Reference
     (P : in out Object_Pointer) return not null access Binary_Object_Type
   with
     Global => null,
     Pre    => not Is_Null (P),
     Post   =>
       not Is_Null (At_End (P))
       and then At_End (Reference'Result).all = Deref (At_End (P));

   function Allocate (O : Binary_Object_Type) return Object_Pointer
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
     Depends        => (P => null, The_Memory => +P),
     Global         => (In_Out => The_Memory),
     Modifies       => (The_Memory when not Is_Null (P)),
     Post           => Is_Null (P),
     Contract_Cases =>
       (Is_Null (P) => Num_Free = Num_Free'Old,
        others      => Num_Free = Num_Free'Old + 1);

private
   pragma SPARK_Mode (Off);

   package Base is new
     Allocator.Base
       (Object_Size        => Object_Size,
        Allocator_Length   => Allocator_Length,
        Binary_Object_Type => Binary_Object_Type,
        Index_Base         => Index_Base);
   use Base;

   type Object_Pointer is record
      Index : Extended_Index := 0;
   end record
   with Predicate => Index >= 0;

   function Is_Null (P : Object_Pointer) return Boolean
   is (P.Index = 0);

end Allocator.Ownership_Wrapper;
