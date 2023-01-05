------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--          SPARK.POINTERS.POINTERS_WITH_ALIASING_SEPARATE_MEMORY           --
--                                                                          --
--                                 B o d y                                  --
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

with Unchecked_Conversion;

package body SPARK.Pointers.Pointers_With_Aliasing_Separate_Memory with
  SPARK_Mode => Off
is
   procedure Dealloc_Obj is new Unchecked_Deallocation (Object, Pointer);
   function Pointer_To_Integer is new
     Unchecked_Conversion (Pointer, Address_Type);

   ---------
   -- "=" --
   ---------

   function "=" (P1, P2 : Pointer) return Boolean is (Eq (P1, P2));

   -------------
   -- Address --
   -------------

   function Address (P : Pointer) return Address_Type is
     (Pointer_To_Integer (P));

   ------------
   -- Assign --
   ------------

   procedure Assign (Memory : in out Memory_Type; P : Pointer; O : Object) is
   begin
      P.all := O;
   end Assign;

   ------------------------
   -- Constant_Reference --
   ------------------------

   function Constant_Reference (Memory : Memory_Type; P : Pointer)
                                return not null access constant Object
   is
     (P);

   ------------
   -- Create --
   ------------

   procedure Create (Memory : in out Memory_Type; O : Object; P : out Pointer)
   is
   begin
      P := new Object'(O);
   end Create;

   -------------
   -- Dealloc --
   -------------

   procedure Dealloc (Memory : in out Memory_Type; P : in out Pointer) is
   begin
      Dealloc_Obj (P);
   end Dealloc;

   -----------
   -- Deref --
   -----------

   function Deref (Memory : Memory_Type; P : Pointer) return Object is (P.all);

   -----------------
   -- Move_Memory --
   -----------------

   procedure Move_Memory (Source, Target : in out Memory_Type; F : Footprint)
   is null;

   ------------------
   -- Null_Pointer --
   ------------------

   function Null_Pointer return Pointer is (null);

   ---------------
   -- Reference --
   ---------------

   function Reference (Memory : not null access Memory_Type; P : Pointer)
                       return   not null access Object
   is
     (P);
end SPARK.Pointers.Pointers_With_Aliasing_Separate_Memory;
