------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--                     SPARK.CONTAINERS.FORMAL.HOLDERS                      --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--          Copyright (C) 2022-2022, Free Software Foundation, Inc.         --
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

private with Ada.Finalization;

private generic
   type Element_Type is private;

package SPARK.Containers.Formal.Holders is

   type Element_Type_Access is access Element_Type;

   type Holder_Type is private;

   function Element (Container : Holder_Type) return Element_Type;
   --  Return the element held by Container

   function Element_Access
     (Container : Holder_Type) return not null access Element_Type;
   --  Return the stored access.

   procedure Replace_Element
     (Container : in out Holder_Type;
      Element   : Element_Type);
   --  Replace the Holder's element by Element and do the required

   procedure Move (Target, Source : in out Holder_Type);
   --  Move the content of the source to the target.

   procedure Adjust (Source : in out Holder_Type);
   --  Make a copy of Container in order to avoid sharing

   procedure Finalize (Container : in out Holder_Type);
   --  Finalize the element held by Container if necessary. It is still
   --  possible to use a finalized Holder_Type but the former value is lost.

private

   type Holder_Type is new Ada.Finalization.Controlled
   with record
      Element : Element_Type_Access;
   end record;
end SPARK.Containers.Formal.Holders;
