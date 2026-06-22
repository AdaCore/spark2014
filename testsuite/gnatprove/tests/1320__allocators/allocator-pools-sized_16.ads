pragma Ada_2022;

with SPARK.Big_Integers; use SPARK.Big_Integers;

--  Per-size wrapper for objects whose smallest fitting bucket is 16 bytes.
--  Stores in bucket 8 and, when With_Promotion is True and bucket 16 is full,
--  transparently promotes to buckets 32, 64. Provides the same API as
--  Allocator.Base.Ownership_Wrapper over the user's Object_Type.
--
--  Object_Bytes is the size of Object_Type in bytes; the user passes it as a
--  static value (it must equal Object_Type'Object_Size / 8, checked at
--  instantiation) and must lie in 9 .. 16 for this wrapper.

generic
   type Object_Type is private;
   Object_Bytes : Positive;
   With_Promotion : Boolean := True;
package Allocator.Pools.Sized_16 with SPARK_Mode is

   pragma
     Compile_Time_Error
       (Object_Bytes /= Object_Type'Object_Size / 8,
        "Object_Bytes is inconsistant with Object_Type");
   pragma
     Compile_Time_Error (Object_Bytes > 16, "Object_Bytes bigger than 16");
   pragma
     Compile_Time_Error (Object_Bytes <= 8, "Object_Bytes smaller than 8");

   --  Object_Pointer is owning structurally (its full view is a record of
   --  owning cell pointers), so no explicit Ownership annotation is needed.
   type Object_Pointer is private
   with Default_Initial_Condition => Is_Null (Object_Pointer);

   function Is_Null (P : Object_Pointer) return Boolean;

   function Is_Promoted_32 (P : Object_Pointer) return Boolean with Ghost;
   function Is_Promoted_64 (P : Object_Pointer) return Boolean with Ghost;
   function Is_Promoted (P : Object_Pointer) return Boolean is
     (Is_Promoted_32 (P)
      or else Is_Promoted_64 (P))
       with Ghost;

   --  Logical equality on Object_Type, used in the value contracts.
   function Obj_Eq (X, Y : Object_Type) return Boolean
   with Ghost, Import, Global => null, Annotate => (GNATprove, Logical_Equal);

   --  Free cells usable by this wrapper: bucket 8, plus (when promoting) the
   --  larger buckets.
   function Num_Free return Big_Natural
   with Ghost, Global => (Memory_16, Memory_32, Memory_64);

   function Deref (P : Object_Pointer) return Object_Type
   with Global => null, Pre => not Is_Null (P);

   function Is_Full return Boolean
   with
     Global => (Memory_16, Memory_32, Memory_64),
     Post   => Is_Full'Result = (Num_Free = 0);

   function Constant_Reference
     (P : Object_Pointer) return not null access constant Object_Type
   with
     Global => null,
     Pre    => not Is_Null (P),
     Post   => Obj_Eq (Constant_Reference'Result.all, Deref (P));

   function At_End
     (X : access constant Object_Type) return access constant Object_Type
   is (X)
   with Ghost, Annotate => (GNATprove, At_End_Borrow);
   function At_End (P : Object_Pointer) return Object_Pointer
   is (P)
   with Ghost, Annotate => (GNATprove, At_End_Borrow);

   function Reference
     (P : in out Object_Pointer) return not null access Object_Type
   with
     Global => null,
     Pre    => not Is_Null (P),
     Post   =>
       not Is_Null (At_End (P))
       and then Obj_Eq (At_End (Reference'Result).all, Deref (At_End (P)));

   function Allocate (O : Object_Type) return Object_Pointer
   with
     Side_Effects,
     Global => (In_Out => (Memory_16, Memory_32, Memory_64)),
     Modifies       =>
       (Memory_16 when Num_Free_16 > 0,
        Memory_32 when Num_Free_16 = 0 and Num_Free_32 > 0,
        Memory_64 when Num_Free_16 = 0 and Num_Free_32 = 0),
     Pre    => Num_Free > 0,
     Post   =>
       Num_Free = Num_Free'Old - 1
       and then not Is_Null (Allocate'Result)
       and then Obj_Eq (Deref (Allocate'Result), O);

   procedure Deallocate (P : in out Object_Pointer)
   with
     Global         => (In_Out => (Memory_16, Memory_32, Memory_64)),
     Modifies       =>
       (Memory_16 when not Is_Null (P) and then not Is_Promoted (P),
        Memory_32 when Is_Promoted_32 (P),
        Memory_64 when Is_Promoted_64 (P),
        P),
     Post           => Is_Null (P),
     Contract_Cases =>
       (Is_Null (P) => Num_Free = Num_Free'Old,
        others      => Num_Free = Num_Free'Old + 1);

private

   package Codec_16 is new Codec (Object_Type, Storage_16, 16, Object_Bytes);
   package Codec_32 is new Codec (Object_Type, Storage_32, 32, Object_Bytes);
   package Codec_64 is new Codec (Object_Type, Storage_64, 64, Object_Bytes);

   --  The object lives in exactly one bucket (or nowhere). A variant record
   --  keyed by the bucket holds a single cell pointer, so it is as small as the
   --  largest underlying pointer plus the discriminant.
   type Bucket_Kind is (None_Bucket, In_16, In_32, In_64);

   type Bucket_Pointer (Kind : Bucket_Kind := None_Bucket) is record
      case Kind is
         when None_Bucket =>
            null;

         when In_16 =>
            P16 : Wrapper_16.Object_Pointer;

         when In_32 =>
            P32 : Wrapper_32.Object_Pointer;

         when In_64 =>
            P64 : Wrapper_64.Object_Pointer;
      end case;
   end record;

   --  Use a wrapper to avoid having to introduce preconditions to enforce that
   --  pointer objects are not constrained.
   type Object_Pointer is record
      Pointer : Bucket_Pointer;
   end record
   with
     Predicate =>
       (if not With_Promotion then Pointer.Kind in None_Bucket | In_16)
       and
         (case Pointer.Kind is
            when None_Bucket => True,
            when In_16       =>
              Wrapper_16.Is_Null (Pointer.P16)
              or else
                Codec_16.From_Raw
                  (Wrapper_16.Deref (Pointer.P16))'Valid_Scalars,
            when In_32       =>
              Wrapper_32.Is_Null (Pointer.P32)
              or else
                Codec_32.From_Raw
                  (Wrapper_32.Deref (Pointer.P32))'Valid_Scalars,
            when In_64       =>
              Wrapper_64.Is_Null (Pointer.P64)
              or else
                Codec_64.From_Raw
                  (Wrapper_64.Deref (Pointer.P64))'Valid_Scalars);

   --  Null when there is no bucket, or when the bucket's cell pointer is null.
   function Is_Null (P : Object_Pointer) return Boolean
   is (case P.Pointer.Kind is
         when None_Bucket => True,
         when In_16       => Wrapper_16.Is_Null (P.Pointer.P16),
         when In_32       => Wrapper_32.Is_Null (P.Pointer.P32),
         when In_64       => Wrapper_64.Is_Null (P.Pointer.P64));

   --------------
   -- Num_Free --
   --------------

   function Num_Free return Big_Natural
   is (Wrapper_16.Num_Free
       + (if With_Promotion
          then Wrapper_32.Num_Free + Wrapper_64.Num_Free
          else 0));

   -------------
   -- Is_Full --
   -------------

   function Is_Full return Boolean
   is (Wrapper_16.Is_Full
       and then
         (if With_Promotion
          then Wrapper_32.Is_Full and then Wrapper_64.Is_Full));

   -----------------
   -- Is_Promoted --
   -----------------

   function Is_Promoted_32 (P : Object_Pointer) return Boolean is
     (P.Pointer.Kind = In_32 and then not Wrapper_32.Is_Null (P.Pointer.P32));
   function Is_Promoted_64 (P : Object_Pointer) return Boolean is
     (P.Pointer.Kind = In_64 and then not Wrapper_64.Is_Null (P.Pointer.P64));

end Allocator.Pools.Sized_16;
