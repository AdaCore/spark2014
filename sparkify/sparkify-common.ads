------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--                       S P A R K I F Y . C O M M O N                      --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2009-2010, AdaCore                     --
--                                                                          --
-- Sparkify is  free  software;  you can redistribute it  and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. Sparkify is distributed in the hope that it will be useful, but --
-- WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHANTABI- --
-- LITY or  FITNESS  FOR A  PARTICULAR  PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- Sparkify is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

--  This package contains declarations of entities which are used in more than
--  one Sparkify component

with Asis;                             use Asis;

with Sparkify.Cursors;                 use Sparkify.Cursors;

package Sparkify.Common is

   ----------------------------------
   -- Useful queries over ASIS API --
   ----------------------------------

   function Declaration_Unique_Name
     (Element : Asis.Element) return Defining_Name;

   --------------------------------------------
   -- Resources needed for source traversing --
   --------------------------------------------

   type Pass is (Effects, Printing);

   Current_Pass : Pass;

   type Phase is (Global_Effects, Printing_Code, Printing_Logic);
   subtype Effects_Phase is Phase range Global_Effects .. Global_Effects;
   subtype Printing_Phase is Phase range Printing_Code .. Printing_Logic;

   type Prefix_Length is range 0 .. 100;

   type Source_Traversal_State is record
      Phase       : Printing_Phase; --  The current phase of printing
      Prefix_Len  : Prefix_Length;
      Prefix      : Wide_String (1 .. Integer (Prefix_Length'Last));
                                    --  Prefix to print for a line
      Echo_Cursor : Cursor;         --  The mark set for a future echo
   end record;

   function Initial_State return Source_Traversal_State;

   type Op_Access is access
      procedure
        (Element :        Asis.Element;
         Control : in out Traverse_Control;
         State   : in out Source_Traversal_State);
   --  Used for look-up tables for specific pre- and post-operations

   procedure No_Action
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State);
   --  Does nothing, may be used as Pre- or Post-Operation

   procedure Non_Implemented_ASIS_2005_Feature
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State);
   --  Raises Fatal_Error

end Sparkify.Common;
