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

--  This package describes the underlying storage strategy for a vector.
--  There are mostly two such strategies (bounded and unbounded) depending on
--  whether the vector has a maximal number of elements.
--
--  Instances of this package only provides the storage, they do not manage
--  the number of elements currently in the vector, for instance.
--
--  They also do not manipulate the Index_Type used to index the vector.
--  Instead, they only manipulate Count_Type indexes, so that we have a full
--  range of integer, and in particular have values to indicate that the node
--  is empty.

pragma Ada_2012;
with Conts.Elements;

package Conts.Vectors.Storage with SPARK_Mode is

   Min_Index : constant Count_Type := Count_Type'First + 1;
   --  Minimal index in vectors.
   --  We use Count_Type'First to indicate a No_Element, so we always start
   --  indexing at 1.

   generic
      with package Elements is new Conts.Elements.Traits (<>);
      --  The type of elements stored in the vector

      type Container (<>) is abstract tagged limited private;
      --  A container for all nodes.
      --  This is used as the ancestor type for the vector types, so that this
      --  type can actually be an unconstrained type (which we could not store
      --  inside another list).

      with procedure Resize
        (Self     : in out Container'Class;
         New_Size : Count_Type;
         Last     : Count_Type;
         Force    : Boolean) is null;
      --  Resize Self so that it has space enough to store New_Size elements.
      --  On exit, Self might actually much larger than requested (if we have
      --  a resize policy of doubling the size of the vector for instance),
      --  or might have be shrunk from its current size if New_Size is smaller.
      --
      --  When a vector has a fixed size, nothing needs to be done.
      --  Otherwise, the vector is free to resize itself as it wants, except
      --  when Force is True in which case that exact size must be used (as
      --  requested by the user).
      --
      --  No memory deallocation for elements takes place, the caller is
      --  responsible for that.
      --  Last is the index of the last valid element already set in the
      --  vector (this is needed so that we only copy the relevant elements).

      with function Max_Capacity (Self : Container'Class) return Count_Type
        is <>;
      --  Maximum number of elements that can be stored in the conainer,
      --  possibly by calling Reserve_Capacity.

      with function Capacity (Self : Container'Class) return Count_Type;
      --  The current capacity of the container

      with procedure Release_Element
        (Self : in out Container'Class; Index : Count_Type);
      --  Free the memory for the node stored at a specific Index.
      --  The element at that index will no longer be used afterward, but there
      --  is not need to mark it explicitly invalid in Self.

      with procedure Release (Self : in out Container'Class) is null;
      --  Free all the memory used by the container.
      --  This does not free the individual elements, since Self itself does
      --  not know the valid range of elements.

      with procedure Set_Element
        (Self    : in out Container'Class;
         Pos     : Count_Type;
         Element : Elements.Stored_Type) is <>;
      with function Get_Element
         (Self : Container'Class;
          Pos  : Count_Type) return Elements.Stored_Type is <>;
      --  Return the element stored at the given position.
      --  Pos will always be a valid position within Self.

      with procedure Assign
        (Self                : in out Container'Class;
         Source              : Container'Class;
         Last                : Count_Type) is <>;
      --  Replace all nodes Min_Index..Last in Nodes with a copy
      --  of the nodes in Source. The elements themselves are copied (via
      --  Elements.Copy).
      --  Self might be the same as Source, this needs to be handled correctly
      --  since this is used when calling Adjust for controlled containers.

      with procedure Copy
        (Self                   : in out Container'Class;
         Source                 : Container'Class;
         Source_From, Source_To : Count_Type;
         Self_From              : Count_Type) is <>;
      --  Copy elements from Source (Source_From..Source_To) to
      --  Self (Self_From .. *).
      --  Copying might be optimized depending on the element traits
      --  attributes. This procedure assumes that Self is large enough to
      --  contain the elements.

   package Traits with SPARK_Mode is
   end Traits;

end Conts.Vectors.Storage;
