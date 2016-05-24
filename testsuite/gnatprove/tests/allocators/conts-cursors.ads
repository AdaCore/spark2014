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

--  This package provides signature packages that describe how to iterate over
--  containers.
--  Such cursors do not provide access to the elements that are in the
--  container, this is done via a separate instance of property maps (see
--  the package Conts.Properties for more information). Separating the two
--  concepts keeps them simpler:
--     We currently provide Forward, Bidirectional and Random_Access cursors
--  If accessing and modifying the elements was built into the concept of
--  cursors, we would need an extra version for all of these to mean
--  Constant_Forward, Constant_Bidirectional and Constant_Random_Access, and
--  perhaps even a concept of Write_Only cursor (for output streams for
--  instance).

pragma Ada_2012;

package Conts.Cursors with SPARK_Mode is

   ---------------------
   -- Forward_Cursors --
   ---------------------
   --  A package that describes how to use forward cursors.  Each container
   --  for which this is applicable provides an instance of this package,
   --  and algorithms should take this package as a generic parameter.

   generic
      type Container_Type (<>) is limited private;
      type Cursor_Type is private;
      with function First (Self : Container_Type) return Cursor_Type is <>;
      with function Has_Element (Self : Container_Type; Pos : Cursor_Type)
         return Boolean is <>;
      with function Next (Self : Container_Type; Pos : Cursor_Type)
         return Cursor_Type is <>;
   package Forward_Cursors is
      subtype Container is Container_Type;
      subtype Cursor    is Cursor_Type;
   end Forward_Cursors;

   ---------------------------
   -- Bidirectional_Cursors --
   ---------------------------

   generic
      type Container_Type (<>) is limited private;
      type Cursor_Type is private;
      with function First (Self : Container_Type) return Cursor_Type is <>;
      with function Has_Element (Self : Container_Type; Pos : Cursor_Type)
         return Boolean is <>;
      with function Next (Self : Container_Type; Pos : Cursor_Type)
         return Cursor_Type is <>;
      with function Previous (Self : Container_Type; Pos : Cursor_Type)
         return Cursor_Type is <>;
   package Bidirectional_Cursors is
      subtype Container is Container_Type;
      subtype Cursor    is Cursor_Type;

      --  A bidirectional cursor is also a forward cursor
      package Forward is new Forward_Cursors (Container, Cursor);
   end Bidirectional_Cursors;

   ----------------------------
   -- Random_Access_Cursors --
   ----------------------------
   --  These are cursors that can access any element from a container, in no
   --  specific order.

   generic
      type Container_Type (<>) is limited private;
      type Index_Type is (<>);

      with function First (Self : Container_Type) return Index_Type is <>;
      --  Index of the first element in the container (often Index_Type'First)
      --  ??? Can we remove this parameter and always use Index_Type'First

      with function Last (Self : Container_Type) return Index_Type is <>;
      --  Return the index of the last valid element in the container.
      --  We do not use a Has_Element function, since having an explicit range
      --  is more convenient for algorithms (for instance to select random
      --  elements in the container).

      with function "-" (Left, Right : Index_Type) return Integer is <>;
      --  Return the number of elements between the two positions.

      with function "+"
        (Left : Index_Type; N : Integer) return Index_Type is <>;
      --  Move Left forward or backward by a number of position.

   package Random_Access_Cursors is
      subtype Container is Container_Type;
      subtype Index     is Index_Type;

      function "-" (Left : Index_Type; N : Integer) return Index_Type
        is (Left + (-N)) with Inline;

      function Next (Self : Container_Type; Idx : Index_Type) return Index_Type
        is (Idx + 1) with Inline;

      function Previous
        (Self : Container_Type; Idx : Index_Type) return Index_Type
        is (Idx - 1) with Inline;

      function Has_Element
        (Self : Container_Type; Idx : Index_Type) return Boolean
        is (Idx >= First (Self) and then Idx <= Last (Self)) with Inline;
      --  This might be made efficient if you pass a First function that
      --  returns a constant and if this contstant is Index_Type'First then
      --  the compiler can simply remove the test.

      --  A random cursor is also a bidirectional and forward cursor
      package Bidirectional is
        new Bidirectional_Cursors (Container, Index_Type);
      package Forward renames Bidirectional.Forward;
   end Random_Access_Cursors;

end Conts.Cursors;
