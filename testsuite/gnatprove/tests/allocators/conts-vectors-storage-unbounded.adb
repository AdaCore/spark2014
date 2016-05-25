------------------------------------------------------------------------------
--                     Copyright (C) 2015-2016, AdaCore                     --
--                                                                          --
-- This library is free software;  you can redistribute it and/or modify it --
-- under terms of the  GNU General Public License  as published by the Free --
-- Software  Foundation;  either version 3,  or (at your  option) any later --
-- version. This library is distributed in the hope that it will be useful, --
-- but WITHOUT ANY WARRANTY;  without even the implied warranty of MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE.                            --
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

pragma Ada_2012;
with Ada.Unchecked_Conversion;
with System;                   use System;
with System.Memory;            use System.Memory;

package body Conts.Vectors.Storage.Unbounded with SPARK_Mode => Off is

   package body Impl is
      pragma Warnings (Off);  --  no aliasing issue
      function Convert is new Ada.Unchecked_Conversion
        (Nodes_Array_Access, System.Address);
      function Convert is new Ada.Unchecked_Conversion
        (System.Address, Nodes_Array_Access);
      pragma Warnings (On);

      procedure Internal_Copy
        (Self                   : Nodes_Array_Access;
         Source                 : Nodes_Array_Access;
         Source_From, Source_To : Count_Type;
         Self_From              : Count_Type) with Inline;
      --  Internal version of Copy, directly applying on an array

      ---------------------
      -- Release_Element --
      ---------------------

      procedure Release_Element
        (Self : in out Container'Class; Index : Count_Type) is
      begin
         Elements.Release (Self.Nodes (Index));
      end Release_Element;

      -----------------
      -- Set_Element --
      -----------------

      procedure Set_Element
        (Self    : in out Container'Class;
         Index   : Count_Type;
         Element : Elements.Stored_Type) is
      begin
         Self.Nodes (Index) := Element;
      end Set_Element;

      -------------------
      -- Internal_Copy --
      -------------------

      procedure Internal_Copy
        (Self                   : Nodes_Array_Access;
         Source                 : Nodes_Array_Access;
         Source_From, Source_To : Count_Type;
         Self_From              : Count_Type) is
      begin
         if Elements.Copyable then
            Self (Self_From .. Self_From + Source_To - Source_From) :=
              Source (Source_From .. Source_To);
         else
            for J in Source_From .. Source_To loop
               Self (Self_From + J - Source_From) :=
                 Elements.Copy (Source (J));
            end loop;
         end if;
      end Internal_Copy;

      ------------
      -- Assign --
      ------------

      procedure Assign
        (Self                : in out Container'Class;
         Source              : Container'Class;
         Last                : Count_Type)
      is
         --  We only allocate enough memory to copy everything. This is
         --  slightly faster, avoid fragmentation, and means Copy can be used
         --  to reduce the memory usage in the application.

         S   : constant size_t := size_t
           (Last * Big_Nodes_Array'Component_Size
            / System.Storage_Unit);

         --  Use a temporary vector in case Self is the same as Source
         Tmp : Nodes_Array_Access;
      begin
         Tmp := Convert (System.Memory.Alloc (S));
         Internal_Copy (Tmp, Source.Nodes, Min_Index, Last, Min_Index);
         Self.Nodes := Tmp;
         Self.Capacity := Source.Capacity;
      end Assign;

      ----------
      -- Copy --
      ----------

      procedure Copy
        (Self                   : in out Container'Class;
         Source                 : Container'Class;
         Source_From, Source_To : Count_Type;
         Self_From              : Count_Type) is
      begin
         Internal_Copy
           (Self.Nodes, Source.Nodes, Source_From, Source_To, Self_From);
      end Copy;

      ------------
      -- Resize --
      ------------

      procedure Resize
        (Self     : in out Container'Class;
         New_Size : Count_Type;
         Last     : Count_Type;
         Force    : Boolean)
      is
         Size : Count_Type;
         S   : size_t;
         Tmp : Nodes_Array_Access;
      begin
         if Force then
            Size := New_Size;
         elsif New_Size < Self.Capacity then
            Size := Resize_Policy.Shrink
              (Current_Size => Self.Capacity, Min_Expected_Size => New_Size);
         else
            Size := Resize_Policy.Grow
              (Current_Size => Self.Capacity, Min_Expected_Size => New_Size);
         end if;

         if Size /= Self.Capacity then
            if Size = 0 then
               System.Memory.Free (Convert (Self.Nodes));
               Self.Nodes := null;
            else
               S := size_t
                 (Size * Big_Nodes_Array'Component_Size / System.Storage_Unit);

               if Self.Nodes = null then
                  Self.Nodes := Convert (System.Memory.Alloc (S));

               elsif Elements.Movable then
                  Self.Nodes := Convert (Realloc (Convert (Self.Nodes), S));

               else
                  Tmp := Convert (System.Memory.Alloc (S));

                  for J in Min_Index .. Count_Type'Min (Last, New_Size) loop
                     Tmp (J) := Elements.Copy (Self.Nodes (J));
                     Elements.Release (Self.Nodes (J));
                  end loop;

                  System.Memory.Free (Convert (Self.Nodes));
                  Self.Nodes := Tmp;
               end if;
            end if;

            Self.Capacity := Size;
         end if;
      end Resize;

      -------------
      -- Release --
      -------------

      procedure Release (Self : in out Container'Class) is
      begin
         System.Memory.Free (Convert (Self.Nodes));
         Self.Nodes := null;
         Self.Capacity := 0;
      end Release;

   end Impl;

end Conts.Vectors.Storage.Unbounded;
