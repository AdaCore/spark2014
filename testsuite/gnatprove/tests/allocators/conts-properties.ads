------------------------------------------------------------------------------
--                     Copyright (C) 2016-2016, AdaCore                     --
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

--  This package describes the concept of property maps.
--  These are an abstract description that explain how to extract information
--  from a container, and possibly set information.
--
--  It is used almost everywhere in this library. Here are some examples:
--
--    * Retrieving stored elements from a container given a cursor.
--      A container of course provides such a capability directly (generally
--      via a function named Element or Get). But the generic algorithms also
--      need to know how to do this operation.
--      Some libraries chose to associate this capability directly with cursors
--      so that a cursor traits package also provides the Get command. But this
--      is slightly inflexible, since containers now need to provide different
--      traits package when they need to return different information (for
--      instance a map could chose to return either the element's key, its
--      value, or a pair of the two. And yet this is the same cursor in all
--      cases.
--
--    * Storing temporary information in the container
--      Graph algorithms typically need to mark vertices when they are visited
--      so that they are not processed again later on.
--      There are two approaches here:
--
--        - Either the container itself is able to store the information
--          directly (in the vertex, the edge, or in some other internal
--          field).
--
--        - Or an external data structure (provided just for the duration of
--          the algorithm) is used. For instance, a vector indexed by a unique
--          integer id associated with the vertices or edges. Or a map.
--
--      In both cases, the algorithm needs to perform the same Set and Get
--      operation. But in the first case, the map is the container itself (and
--      most likely the Clear operation will do nothing). These are called
--      "internal maps".
--
--  Such internal maps are exactly what is used to retrieve an element stored
--  in the container, as described in the first bullet above. But instead of
--  just relying on a primitive operation of the container (which would limit
--  the reusability of the algorithm to other data structures), or a Get
--  formal parameter that assumes the map is the container, the algorithms
--  generally let users decide where the map is stored.
--  This provides one level of indirection (with no performance cost in the
--  general case), which is sometimes useful to reuse algorithms.
--
--  In general, multiple versions of the algorithms will be provided, one for
--  each type of map (interior or exterior), and one that takes the map
--  explicitly in parameter so that the algorithm does not need to create the
--  map on its own, and the container can act as its own map.

pragma Ada_2012;

package Conts.Properties is

   -----------------------------
   -- Read-only property maps --
   -----------------------------

   generic
      type Map_Type (<>) is limited private;
      type Key_Type (<>) is limited private;
      type Value_Type (<>) is private;
      with function Get (M : Map_Type; K : Key_Type) return Value_Type is <>;

   package Read_Only_Maps is
      subtype Map is Map_Type;
      subtype Key is Key_Type;
      subtype Value is Value_Type;
   end Read_Only_Maps;

   -------------------
   -- Property maps --
   -------------------

   generic
      type Map_Type (<>) is limited private;
      type Key_Type (<>) is limited private;
      type Value_Type is private;
      with procedure Set
         (M : in out Map_Type; K : Key_Type; V : Value_Type) is <>;
      with function Get (M : Map_Type; K : Key_Type) return Value_Type is <>;
      with procedure Clear (M : in out Map_Type) is null;
   package Maps is
      subtype Map is Map_Type;
      subtype Key is Key_Type;
      subtype Value is Value_Type;

      package As_Read_Only is new Read_Only_Maps (Map, Key, Value);
   end Maps;

end Conts.Properties;
