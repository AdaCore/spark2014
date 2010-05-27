------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--                       S P A R K I F Y . C O M M O N                      --
--                                                                          --
--                                 B o d y                                  --
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

with Ada.Strings.Wide_Fixed;           use Ada.Strings.Wide_Fixed;
with Ada.Strings;                      use Ada.Strings;

with Asis.Declarations;                use Asis.Declarations;
with Asis.Text;                        use Asis.Text;

with ASIS_UL.Common;

package body Sparkify.Common is

   -----------------------------
   -- Declaration_Unique_Name --
   -----------------------------

   function Declaration_Unique_Name
     (Element : Asis.Declaration) return Wide_String
   is
      Names : constant Defining_Name_List := Asis.Declarations.Names (Element);
   begin
      pragma Assert (Names'Length = 1);
      return Defining_Name_Image (Names (Names'First));
   end Declaration_Unique_Name;

   ------------------
   -- Element_Name --
   ------------------

   function Element_Name (Element : Asis.Element) return Wide_String is
   begin
      return Trim (Element_Image (Element), Left);
   end Element_Name;

   ---------------------------------------
   -- Non_Implemented_ASIS_2005_Feature --
   ---------------------------------------

   procedure Non_Implemented_ASIS_2005_Feature
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
   begin
      raise ASIS_UL.Common.Fatal_Error;
   end Non_Implemented_ASIS_2005_Feature;

   -------------------
   -- Initial_State --
   -------------------

   function Initial_State return Source_Traversal_State is
      Initial_Phase : Phase;
   begin
      case Current_Pass is
         when Effects => Initial_Phase := Global_Effects;
         when Printing => Initial_Phase := Printing_Code;
      end case;

      return
        (Phase       => Initial_Phase,
         Prefix_Len  => 0,
         Prefix      => (others => ' '),
         Echo_Cursor => File_Cursor (Kind => Before_File));
   end Initial_State;

   ---------------
   -- No_Action --
   ---------------

   procedure No_Action
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
   begin
      pragma Unreferenced (Element);
      pragma Unreferenced (Control);
      pragma Unreferenced (State);
      null;
   end No_Action;

end Sparkify.Common;
