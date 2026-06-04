with Ada.Unchecked_Conversion;
with Interfaces; use Interfaces;

procedure Test with SPARK_Mode is

   type Byte_Array is array (Positive range <>) of Unsigned_8;

   subtype Byte_Array_8 is Byte_Array (1 .. 8);

   type Binary_Object_Type is record
      Data : Byte_Array_8;
   end record
   with Alignment => 8;

   function Real_Eq (X, Y : Binary_Object_Type) return Boolean
   with Annotate => (GNATprove, Logical_Equal), Global => null, Import;

   type Binary_Object_Pointer is not null access Binary_Object_Type;

   function At_End
     (X : access constant Binary_Object_Type)
      return access constant Binary_Object_Type
   is (X)
   with Ghost, Annotate => (GNATprove, At_End_Borrow);

   function Reference
     (P : in out Binary_Object_Pointer)
      return not null access Binary_Object_Type
   with
     Global => null,
     Post   => Real_Eq (At_End (Reference'Result).all, At_End (P).all),
     Import;

   type Object_Type is record
      F1 : Integer_32;
      F2 : Unsigned_16;
      F3 : Boolean;
      F4 : Integer_8;
   end record
   with Object_Size => 64;

   function Valid_Object (X : Binary_Object_Type) return Boolean
   with Global => null, Import;

   type Object_Pointer is record
      Ptr : Binary_Object_Pointer;
   end record
   with Predicate => Valid_Object (Ptr.all);

   function At_End
     (X : access constant Object_Type) return access constant Object_Type
   is (X)
   with Ghost, Annotate => (GNATprove, At_End_Borrow);

   function Convert_Access
     (Source : not null access Binary_Object_Type)
      return not null access Object_Type
   with
     Import,
     Global => null,
     Pre    => Valid_Object (Source.all),
     Post   => Valid_Object (At_End (Source).all);

   function Reference
     (P : in out Object_Pointer) return not null access Object_Type is
   begin
      return Convert_Access (Reference (P.Ptr));
   end Reference;

begin
   null;
end Test;
