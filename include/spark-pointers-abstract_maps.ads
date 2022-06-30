------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--          S P A R K . P O I N T E R S . A B S T R A C T _ M A P S         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2022-2022, AdaCore                     --
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

--  Introduce a non executable type for maps with size 0. It can be used to
--  model a ghost subprogram parameter or a ghost component.

generic
   type Key_Type is private;
   No_Key : Key_Type;
   type Object_Type (<>) is private;

package SPARK.Pointers.Abstract_Maps with
  SPARK_Mode,
  Annotate => (GNATprove, Always_Return)
is

   type Map is private with
     Default_Initial_Condition => Is_Empty (Map),
     Iterable                  => (First       => Iter_First,
                                   Next        => Iter_Next,
                                   Has_Element => Has_Key);

   function Empty_Map return Map with
     Global => null,
     Post   => Is_Empty (Empty_Map'Result);

   function Has_Key (M : Map; K : Key_Type) return Boolean with
     Import,
     Global => null,
     Post   => (if Has_Key'Result then K /= No_Key);

   function Get (M : Map; K : Key_Type) return Object_Type with
     Import,
     Global => null,
     Pre    => Has_Key (M, K);

   --  For quantification only. Do not use to iterate through the map.
   function Iter_First (M : Map) return Key_Type with
     Global => null,
     Import;
   function Iter_Next (M : Map; K : Key_Type) return Key_Type with
     Global => null,
     Import;

   pragma Warnings (Off, "unused variable ""K""");
   function Is_Empty (M : Map) return Boolean is
     (for all K in M => False)
   with
     Global => null;

   type Ownership_Map is private with
     Annotate => (GNATprove, Ownership, "Needs_Reclamation");

   function "+" (M : Ownership_Map) return Map with
     Global => null;

   pragma Warnings (Off, "unused variable ""K""");
   function Is_Empty (M : Ownership_Map) return Boolean is
     (for all K in +M => False)
   with
     Global   => null,
     Annotate => (GNATprove, Ownership, "Is_Reclaimed");

   function Empty_Map return Ownership_Map with
     Global => null,
     Post => Is_Empty (Empty_Map'Result);

private
   pragma SPARK_Mode (Off);

   type Map is null record;

   function Empty_Map return Map is ((others => <>));

   type Ownership_Map is new Map;

   function "+" (M : Ownership_Map) return Map is
     (Map (M));

   function Empty_Map return Ownership_Map is ((others => <>));
end SPARK.Pointers.Abstract_Maps;
