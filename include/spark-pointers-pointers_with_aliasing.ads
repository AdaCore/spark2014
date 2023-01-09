------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--                      S P A R K . P O I N T E R S .                       --
--                P O I N T E R S _ W I T H _ A L I A S I N G               --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2022-2023, AdaCore                     --
--                                                                          --
-- SPARK is free software;  you can  redistribute it and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion. SPARK is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.                                     --
--                                                                          --
-- As a special exception under Section 7 of GPL version 3, you are granted --
-- additional permissions described in the GCC Runtime Library Exception,   --
-- version 3.1, as published by the Free Software Foundation.               --
--                                                                          --
-- You should have received a copy of the GNU General Public License and    --
-- a copy of the GCC Runtime Library Exception along with this program;     --
-- see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see    --
-- <http://www.gnu.org/licenses/>.                                          --
--                                                                          --
------------------------------------------------------------------------------

with Interfaces; use Interfaces;
with SPARK.Pointers.Abstract_Maps;

generic
   type Object (<>) is private;
package SPARK.Pointers.Pointers_With_Aliasing with
  SPARK_Mode,
  Annotate          => (GNATprove, Always_Return),
  Initial_Condition =>
    (for all A in Address_Type => not Valid (Memory, A))
    --  The memory is initially empty
is
   pragma Unevaluated_Use_Of_Old (Allow);

   --  Identity function on objects. As the library copies objects inside
   --  code annotated with SPARK_Mode => Off, we need to make sure that such
   --  copies are allowed by SPARK.
   function Check_No_Deep_Objects (O : Object) return Object is (O) with Ghost;

   --  Model for the memory, this is not executable

   package Memory_Model is
      type Address_Type is new Unsigned_64;
      --  Address type on 64 bits machines

      package Address_To_Object_Maps is new Abstract_Maps
        (Address_Type, 0, Object);
      --  Use an abstract map rather than a functional map to avoid taking up
      --  memory space as the memory model cannot be ghost.

      type Memory_Type is new Address_To_Object_Maps.Map;

      --  Whether an address designates some valid data in the memory
      function Valid (M : Memory_Type; A : Address_Type) return Boolean renames
        Has_Key;

      function Object_Logic_Equal (Left, Right : Object) return Boolean with
        Ghost,
        Import,
        Global => null,
        Annotate => (GNATprove, Logical_Equal);
      --  Logical equality on objects. It is marked as import as it cannot be
      --  safely executed on most object types.

      --  Functions to make it easier to specify the frame of subprograms
      --  modifying a memory.

      type Addresses is array (Address_Type) of Boolean with Ghost;

      function None return Addresses is
        ([others => False])
      with Ghost;
      function Only (A : Address_Type) return Addresses is
        ([for Q in Address_Type => (Q = A)])
      with Ghost;

      function Writes
        (M1, M2 : Memory_Type; Target : Addresses) return Boolean
      is
        (for all A in Address_Type =>
           (if not Target (A) and Valid (M1, A) and Valid (M2, A)
            then Object_Logic_Equal (Get (M1, A), Get (M2, A))))
      with Ghost;

      function Allocates
        (M1, M2 : Memory_Type; Target : Addresses) return Boolean
      is
        ((for all A in Address_Type =>
            (if Valid (M2, A) then Target (A) or Valid (M1, A)))
         and (for all A in Address_Type =>
                  (if Target (A) then not Valid (M1, A) and Valid (M2, A))))
      with Ghost;

      function Deallocates
        (M1, M2 : Memory_Type; Target : Addresses) return Boolean
      is
        ((for all A in Address_Type =>
            (if Valid (M1, A) then Target (A) or Valid (M2, A)))
         and (for all A in Address_Type =>
                  (if Target (A) then not Valid (M2, A) and Valid (M1, A))))
      with Ghost;

   end Memory_Model;

   use Memory_Model;
   Memory : aliased Memory_Type;
   --  The memory cannot be ghost, as it occurs as a parameter of calls to
   --  Constant_Reference and Reference functions so they can be traversal
   --  functions.

   type Pointer is private with
     Default_Initial_Condition => Address (Pointer) = 0;
   function Null_Pointer return Pointer with
     Global => null,
     Post   => Address (Null_Pointer'Result) = 0;
   function Address (P : Pointer) return Address_Type with
     Global => null;

   function "=" (P1, P2 : Pointer) return Boolean with
     Global   => null,
     Post     => "="'Result = (Address (P1) = Address (P2)),
     Annotate => (GNATprove, Inline_For_Proof);

   procedure Create (O : Object; P : out Pointer) with
     Global => (In_Out => Memory),
     Post   =>
       Valid (Memory, Address (P))
         and then Allocates (Memory'Old, Memory, Only (Address (P)))
         and then Deallocates (Memory'Old, Memory, None)
         and then Writes (Memory'Old, Memory, None)
         and then Object_Logic_Equal (Deref (P), O);

   --  Primitives for classical pointer functionalities. Deref will copy the
   --  designated value.

   function Deref (P : Pointer) return Object with
     Global   => Memory,
     Pre      => Valid (Memory, Address (P)),
     Post     => Deref'Result = Get (Memory, Address (P)),
     Annotate => (GNATprove, Inline_For_Proof);

   procedure Assign (P : Pointer; O : Object) with
     Global => (In_Out => Memory),
     Pre    => Valid (Memory, Address (P)),
     Post   =>
       Object_Logic_Equal (Get (Memory, Address (P)), O)
         and then Allocates (Memory'Old, Memory, None)
         and then Deallocates (Memory'Old, Memory, None)
         and then Writes (Memory'Old, Memory, Only (Address (P)));

   procedure Dealloc (P : in out Pointer) with
     Global => (In_Out => Memory),
     Pre    => Valid (Memory, Address (P)) or P = Null_Pointer,
     Post   =>
       P = Null_Pointer
         and then Allocates (Memory'Old, Memory, None)
         and then
           (if P'Old = Null_Pointer
            then Deallocates (Memory'Old, Memory, None)
            else Deallocates (Memory'Old, Memory, Only (Address (P)'Old)))
         and then Writes (Memory'Old, Memory, None);

   --  Primitives to access the content of a memory cell directly. Ownership is
   --  used to preserve the link between the dereferenced value and the
   --  memory model.

   function Constant_Reference (Memory : Memory_Type; P : Pointer)
                                return not null access constant Object
   with
     Global => null,
     Pre    => Valid (Memory, Address (P)),
     Post   =>
       Object_Logic_Equal
         (Constant_Reference'Result.all, Get (Memory, Address (P)));

   function At_End (X :    access constant Object)
                    return access constant Object
   is
     (X)
   with
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function At_End (X :    access constant Memory_Type)
                    return access constant Memory_Type
   is
     (X)
   with
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function Reference (Memory : not null access Memory_Type; P : Pointer)
                       return   not null access Object
   with
     Global => null,
     Pre    => Valid (Memory.all, Address (P)),
     Post   =>
       Object_Logic_Equal
         (At_End (Reference'Result).all,
          Get (At_End (Memory).all, Address (P)))
         and then Allocates (Memory.all, At_End (Memory).all, None)
         and then Deallocates (Memory.all, At_End (Memory).all, None)
         and then Writes (Memory.all, At_End (Memory).all, Only (Address (P)));

private
   pragma SPARK_Mode (Off);
   type Pointer_B is access Object;
   function Eq (P1, P2 : Pointer_B) return Boolean renames "=";
   type Pointer is new Pointer_B;
end SPARK.Pointers.Pointers_With_Aliasing;
